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
using sta::Delay;
// using sta::fuzzyInf;


void
Resizer::helloworld()
{
	printf("Hello world!");
}

void
Resizer::worstFailingPaths(
		// Return values.
		Slack &worst_slack,
		Vertex *&worst_vertex)
{
	
	report_->reportLine("Worst failing paths: ");
	init();
	resizePreamble();
	
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
		sta_->worstSlack(max_, worst_slack, worst_vertex);
		report_->reportLine("%s slack = %s worst_slack = %s",
				end->name(network_),
				delayAsString(end_slack, sta_, digits),
				delayAsString(worst_slack, sta_, digits));
		end_index++;
		if (end_index > max_end_count)
			break;

		PathRef end_path = sta_->vertexWorstSlackPath(end, max_);

		bool changed = swapVT(end_path, end_slack);

        // resizer_->updateParasitics();
        // sta_->findRequireds();
		end_slack = sta_->vertexSlack(end, max_);
		sta_->worstSlack(max_, worst_slack, worst_vertex);

		if (end_index == 1)
			end = worst_vertex;

	}
} 



bool
Resizer::swapVT(PathRef &path, Slack path_slack)
{
	PathExpanded expanded(&path, sta_);
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

		sort(load_delays.begin(), load_delays.end(),
			[](pair<int, Delay> pair1,
			   pair<int, Delay> pair2) {
			return pair1.second > pair2.second
				|| (pair1.second == pair2.second
					&& pair1.first > pair2.first);
			});

		// Attack gates with largest load delays first.
		for (const auto& [drvr_index, ignored] : load_delays) {
			PathRef *drvr_path = expanded.path(drvr_index);
			Vertex *drvr_vertex = drvr_path->vertex(sta_);
			const Pin *drvr_pin = drvr_vertex->pin();
			const Net *net = network_->net(drvr_pin);
			LibertyPort *drvr_port = network_->libertyPort(drvr_pin);
			LibertyCell *drvr_cell = drvr_port ? drvr_port->libertyCell() : nullptr;
			// int fanout = this->fanout(drvr_vertex);
			// debugPrint(logger_, RSZ, "resizer", 3, "{} {} fanout = {}",
			// 			network_->pathName(drvr_pin),
			// 			drvr_cell ? drvr_cell->name() : "none", fanout);

			report_->reportLine("resizer = %s %s \n", network_->pathName(drvr_pin), drvr_cell ? drvr_cell->name() : "none");

			if (swapVTDrvr(drvr_path, drvr_index, &expanded)) {
				changed = true;
				break;
			}

		}
	}



	return changed;
}

bool
Resizer::swapVTDrvr(PathRef *drvr_path,
                        int drvr_index,
                        PathExpanded *expanded)
{
	report_->reportLine("swapVTDrvr called\n");

	Pin *drvr_pin = drvr_path->pin(this);
	Instance *drvr = network_->instance(drvr_pin);
	const DcalcAnalysisPt *dcalc_ap = drvr_path->dcalcAnalysisPt(sta_);
	float load_cap = graph_delay_calc_->loadCap(drvr_pin, dcalc_ap);
	int in_index = drvr_index - 1;
	PathRef *in_path = expanded->path(in_index);
	Pin *in_pin = in_path->pin(sta_);
	LibertyPort *in_port = network_->libertyPort(in_pin);
	if (!this->dontTouch(drvr)) {
		float prev_drive;
		if (drvr_index >= 2) {
			int prev_drvr_index = drvr_index - 2;
			PathRef *prev_drvr_path = expanded->path(prev_drvr_index);
			Pin *prev_drvr_pin = prev_drvr_path->pin(sta_);
			prev_drive = 0.0;
			LibertyPort *prev_drvr_port = network_->libertyPort(prev_drvr_pin);
			if (prev_drvr_port) {
				prev_drive = prev_drvr_port->driveResistance();
			}
		}
		else { prev_drive = 0.0; }

		LibertyPort *drvr_port = network_->libertyPort(drvr_pin);
		LibertyCell *upsize = swapVTCell(in_port, drvr_port, load_cap,
										prev_drive, dcalc_ap);
		// if (upsize) {
		// 	debugPrint(logger_, RSZ, "repair_setup", 3, "resize {} {} -> {}",
		// 				network_->pathName(drvr_pin),
		// 				drvr_port->libertyCell()->name(),
		// 				upsize->name());
		// 	if (!this->dontTouch(drvr)
		// 		&& resizer_->replaceCell(drvr, upsize, true)) {
		// 		resize_count_++;
		// 		return true;
		// 	}
		// }
	}
    return false;
}

LibertyCell *
Resizer::swapVTCell(LibertyPort *in_port,
                        LibertyPort *drvr_port,
                        float load_cap,
                        float prev_drive,
                        const DcalcAnalysisPt *dcalc_ap)
{

	report_->reportLine("swapVTCell called\n");

	// diff library for each characterization

	int lib_ap = dcalc_ap->libertyIndex();
	LibertyCell *cell = drvr_port->libertyCell();
	report_->reportLine("cell: %s\n", cell->name());
	LibertyCellSeq *equiv_cells = sta_->equivCells(cell);

	if (equiv_cells) {
		report_->reportLine("equiv cells: \n");
		const char *in_port_name = in_port->name();
		const char *drvr_port_name = drvr_port->name();
		// sort(equiv_cells,
		// 	[=] (const LibertyCell *cell1,
		// 		const LibertyCell *cell2) {
		// 	LibertyPort *port1=cell1->findLibertyPort(drvr_port_name)->cornerPort(lib_ap);
		// 	LibertyPort *port2=cell2->findLibertyPort(drvr_port_name)->cornerPort(lib_ap);
		// 	float drive1 = port1->driveResistance();
		// 	float drive2 = port2->driveResistance();
		// 	ArcDelay intrinsic1 = port1->intrinsicDelay(this);
		// 	ArcDelay intrinsic2 = port2->intrinsicDelay(this);
		// 	return drive1 > drive2
		// 		|| ((drive1 == drive2
		// 			&& intrinsic1 < intrinsic2)
		// 			|| (intrinsic1 == intrinsic2
		// 				&& port1->capacitance() < port2->capacitance()));
		// 	});
		float drive = drvr_port->cornerPort(lib_ap)->driveResistance();
		float delay = this->gateDelay(drvr_port, load_cap, this->tgt_slew_dcalc_ap_)
		+ prev_drive * in_port->cornerPort(lib_ap)->capacitance();
		for (LibertyCell *equiv : *equiv_cells) {
			LibertyCell *equiv_corner = equiv->cornerCell(lib_ap);
			LibertyPort *equiv_drvr = equiv_corner->findLibertyPort(drvr_port_name);
			LibertyPort *equiv_input = equiv_corner->findLibertyPort(in_port_name);
			float equiv_drive = equiv_drvr->driveResistance();
			// Include delay of previous driver into equiv gate.
			float equiv_delay = this ->gateDelay(equiv_drvr, load_cap, dcalc_ap)
				+ prev_drive * equiv_input->capacitance();
			report_->reportLine("cell name: %s    in_port name: %s    drvr_por name: %s    equiv_drive = %f    equiv_delay = %f\n",
								equiv->name(), drvr_port_name, equiv_drive, equiv_delay);
			if (repair_setup_->meetsSizeCriteria(cell, equiv, true)) {
				report_->reportLine("Meets size criteria");
			}
			if (!this->dontUse(equiv)
				&& equiv_drive < drive
				&& equiv_delay < delay)
				return equiv;
			}
	}
  return nullptr;
}
} // namespace
