/////////////////////////////////////////////////////////////////////////////
//
// Copyright (c) 2019, The Regents of the University of California
// All rights reserved.
//
// BSD 3-Clause License
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//
// * Redistributions of source code must retain the above copyright notice, this
//   list of conditions and the following disclaimer.
//
// * Redistributions in binary form must reproduce the above copyright notice,
//   this list of conditions and the following disclaimer in the documentation
//   and/or other materials provided with the distribution.
//
// * Neither the name of the copyright holder nor the names of its
//   contributors may be used to endorse or promote products derived from
//   this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
// AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
// ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
// LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
// CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
// SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
// INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
// CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
// POSSIBILITY OF SUCH DAMAGE.
//
///////////////////////////////////////////////////////////////////////////////

#include "RepairSetup.hh"
#include "BufferedNet.hh"
#include "rsz/Resizer.hh"

#include "utl/Logger.h"
#include "db_sta/dbNetwork.hh"

#include "sta/Units.hh"
#include "sta/Liberty.hh"
#include "sta/TimingArc.hh"
#include "sta/Graph.hh"
#include "sta/DcalcAnalysisPt.hh"
#include "sta/GraphDelayCalc.hh"
#include "sta/Parasitics.hh"
#include "sta/Sdc.hh"
#include "sta/InputDrive.hh"
#include "sta/Corner.hh"
#include "sta/PathVertex.hh"
#include "sta/PathRef.hh"
#include "sta/PathExpanded.hh"
#include "sta/Fuzzy.hh"
#include "sta/PortDirection.hh"

// #include "sta/Search.hh"
// #include "sta/search/WorstSlack.hh"

namespace rsz {

using std::abs;
using std::min;
using std::max;
using std::string;
using std::vector;
using std::map;
using std::pair;
using std::make_shared;

using utl::RSZ;

using sta::VertexOutEdgeIterator;
using sta::Edge;
using sta::Clock;
using sta::PathExpanded;
using sta::INF;
using sta::fuzzyEqual;
using sta::fuzzyLess;
using sta::fuzzyLessEqual;
using sta::fuzzyGreater;
using sta::fuzzyGreaterEqual;
using sta::Unit;
using sta::Corners;
using sta::InputDrive;

using sta::Unit;
using sta::Units;
using sta::Port;
using sta::PinSeq;
using sta::PinSet;
using sta::NetConnectedPinIterator;
using sta::PathAnalysisPt;
// using sta::fuzzyInf;


void
Resizer::helloworld()
{
	printf("Hello world!");
}

void
Resizer::worstFailingPaths(const MinMax *min_max,
		// Return values.
		Slack &worst_slack,
		Vertex *&worst_vertex)
{
	report_->reportLine("Worst failing paths: ");
	// report_->reportLine("Inside failing paths function");

	// Resizer::resizeSlackPreamble();
	// Resizer::findResizeSlacks1();
	init();
	constexpr int digits = 3;

	buffer_moved_into_core_ = false;

	  // Sort failing endpoints by slack.
	VertexSet *endpoints = sta_->endpoints();
	VertexSeq violating_ends;
	for (Vertex *end : *endpoints) {
		Slack end_slack = sta_->vertexSlack(end, max_);
		if (end_slack < 0.0)
		violating_ends.push_back(end);
	}
	sort(violating_ends, [=](Vertex *end1, Vertex *end2) {
		return sta_->vertexSlack(end1, max_) < sta_->vertexSlack(end2, max_);
	});

	report_->reportLine("Report:");
	report_->reportLine("Violating endpoints %d/%d",
		violating_ends.size(), endpoints->size());

	
	int end_index = 0;
	// int max_end_count = violating_ends.size() * repair_tns_end_percent;
	int max_end_count = 1;
	// Always repair the worst endpoint, even if tns percent is zero.
	max_end_count = max(max_end_count, 1);
	incrementalParasiticsBegin();
	for (Vertex *end : violating_ends) {
		updateParasitics();
		sta_->findRequireds();
		Slack end_slack = sta_->vertexSlack(end, max_);
		Slack worst_slack;
		Vertex *worst_vertex;
		sta_->worstSlack(max_, worst_slack, worst_vertex);
		report_->reportLine("%s slack = %s worst_slack = %s",
				end->name(network_),
				delayAsString(end_slack, sta_, digits),
				delayAsString(worst_slack, sta_, digits));
		end_index++;
		if (end_index > max_end_count)
			break;

		PathRef end_path = sta_->vertexWorstSlackPath(end, max_);

		PathExpanded expanded(&end_path, sta_);
		bool changed = false;
		if (expanded.size() > 1) {
			int path_length = expanded.size();
			vector<pair<int, Delay>> load_delays;
			int start_index = expanded.startIndex();
			
			
			// Find load delay for each gate in the path.
			for (int i = start_index; i < path_length; i++) {
			PathRef *path = expanded.path(i);
			Vertex *path_vertex = path->vertex(sta_);
			const DcalcAnalysisPt *dcalc_ap = path->dcalcAnalysisPt(sta_);
			int lib_ap = dcalc_ap->libertyIndex();

			const Pin *path_pin = path->pin(sta_);
			if (i > 0
				&& network_->isDriver(path_pin)
				&& !network_->isTopLevelPort(path_pin)) {
				TimingArc *prev_arc = expanded.prevArc(i);
				const TimingArc *corner_arc = prev_arc->cornerArc(lib_ap);
				Edge *prev_edge = path->prevEdge(prev_arc, sta_);
				Delay load_delay_w_intrinsic = graph_->arcDelay(prev_edge, prev_arc, dcalc_ap->index());
				Delay load_delay = graph_->arcDelay(prev_edge, prev_arc, dcalc_ap->index())
				// Remove intrinsic delay to find load dependent delay.
				- corner_arc->intrinsicDelay();
				load_delays.push_back(pair(i, load_delay));
				debugPrint(logger_, RSZ, "repair_setup", 3, "{} load_delay = {}",
						path_vertex->name(network_),
						delayAsString(load_delay, sta_, 3));
				report_->reportLine("%s load_delay = %s, load_delay_w_intrinsic = %s\n", path_vertex->name(network_), delayAsString(load_delay, sta_, 3), delayAsString(load_delay_w_intrinsic, sta_, 3));
				}
    		}

	// 	LibertyCell *cell = drvr_port->libertyCell();
	// 	LibertyCellSeq *equiv_cells = sta_->equivCells(cell);
	// float drive = drvr_port->cornerPort(lib_ap)->driveResistance();
    // float delay = resizer_->gateDelay(drvr_port, load_cap, resizer_->tgt_slew_dcalc_ap_)
    //   + prev_drive * in_port->cornerPort(lib_ap)->capacitance();
    // for (LibertyCell *equiv : *equiv_cells) {
    //   LibertyCell *equiv_corner = equiv->cornerCell(lib_ap);
    //   LibertyPort *equiv_drvr = equiv_corner->findLibertyPort(drvr_port_name);
    //   LibertyPort *equiv_input = equiv_corner->findLibertyPort(in_port_name);
    //   float equiv_drive = equiv_drvr->driveResistance();
    //   // Include delay of previous driver into equiv gate.
    //   float equiv_delay = resizer_->gateDelay(equiv_drvr, load_cap, dcalc_ap)
    //     + prev_drive * equiv_input->capacitance();
	// 	}

		end_slack = sta_->vertexSlack(end, max_);
		sta_->worstSlack(max_, worst_slack, worst_vertex);

		if (end_index == 1)
			end = worst_vertex;

        }
    } 

}

	
	// sta::PathAPIndex path_ap_count = sta_->corners()->pathAnalysisPtCount();
	// for (sta::PathAPIndex i = 0; i < path_ap_count; i++) {
	// 	// worst_slacks_[path_ap_index].worstSlack(path_ap_index, worst_slack_0, worst_vertex_0);
	// 	report_->reportLine("PathAPIndex i = %d, Slack = %f", i, worst_slack_0);
	// }

 	// for (auto net : worst_slack_nets_)
	//  	report_->reportLine("Net: %f", net_slack_map_[net]);
    	

	// Get worst_slack_nets_ and iterate through?

	// IGNORE BELOW, just some potentially useful snippets of code from other functions.
	// searchPreamble();
	// Slack worst_slack_0;
	// Vertex *worst_vertex_0;
	// search_->worstSlack(min_max, worst_slack_0, worst_vertex_0);
	// vertexWorstSlackPath(worst_vertex_0, nullptr, min_max);

	// worstSlackPreamble();
    // worst_slacks_->worstSlack(min_max, worst_slack, worst_vertex);

	// tnsPreamble();
	// Slack tns = 0.0;
	// for (Corner *corner : *corners_) {
	//   PathAPIndex path_ap_index = corner->findPathAnalysisPt(min_max)->index();
	//   Slack tns1 = tns_[path_ap_index];
	//   if (delayLess(tns1, tns, this))
	//     tns = tns1;
	// }
	// return tns;




} // namespace
