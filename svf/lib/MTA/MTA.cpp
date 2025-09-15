//===- MTA.h -- Analysis of multithreaded programs-------------//
//
//                     SVF: Static Value-Flow Analysis
//
// Copyright (C) <2013->  <Yulei Sui>
//

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.

// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
//
//===----------------------------------------------------------------------===//


/*
 * MTA.cpp
 *
 *  Created on: May 14, 2014
 *      Author: Yulei Sui, Peng Di
*/

#include "Util/Options.h"
#include "MTA/MTA.h"
#include "MTA/MHP.h"
#include "MTA/TCT.h"
#include "MTA/LockAnalysis.h"
#include "MTA/MTAStat.h"
#include "WPA/Andersen.h"
#include "MTA/FSMPTA.h"
#include "Util/SVFUtil.h"

using namespace SVF;
using namespace SVFUtil;

MTA::MTA() : tcg(nullptr), tct(nullptr), mhp(nullptr), lsa(nullptr)
{
    stat = std::make_unique<MTAStat>();
}

MTA::~MTA()
{
    if (tcg)
        delete tcg;
    //if (tct)
    //    delete tct;
    delete mhp;
    delete lsa;
}

/*!
 * Perform data race detection
 */
bool MTA::runOnModule(SVFIR* pag)
{
    mhp = computeMHP(pag->getModule());
    lsa = computeLocksets(mhp->getTCT());

    if(Options::RaceCheck())
        detect(pag->getModule());
    /*
    if (Options::AndersenAnno()) {
        pta = mhp->getTCT()->getPTA();
        if (pta->printStat())
            stat->performMHPPairStat(mhp,lsa);
        AndersenWaveDiff::releaseAndersenWaveDiff();
    } else if (Options::FSAnno()) {

        reportMemoryUsageKB("Mem before analysis");
        DBOUT(DGENERAL, outs() << pasMsg("FSMPTA analysis\n"));
        DBOUT(DMTA, outs() << pasMsg("FSMPTA analysis\n"));

        DOTIMESTAT(double ptStart = stat->getClk());
        pta = FSMPTA::createFSMPTA(module, mhp,lsa);
        DOTIMESTAT(double ptEnd = stat->getClk());
        DOTIMESTAT(stat->FSMPTATime += (ptEnd - ptStart) / TIMEINTERVAL);

        reportMemoryUsageKB("Mem after analysis");

        if (pta->printStat())
            stat->performMHPPairStat(mhp,lsa);

        FSMPTA::releaseFSMPTA();
    }

    if (DoInstrumentation) {
        DBOUT(DGENERAL, outs() << pasMsg("ThreadSanitizer Instrumentation\n"));
        DBOUT(DMTA, outs() << pasMsg("ThreadSanitizer Instrumentation\n"));
        TSan tsan;
        tsan.doInitialization(*pta->getModule());
        for (Module::iterator it = pta->getModule()->begin(), eit = pta->getModule()->end(); it != eit; ++it) {
            tsan.runOnFunction(*it);
        }
        if (pta->printStat())
            PrintStatistics();
    }
    */

    return false;
}

/*!
 * Compute lock sets
 */
LockAnalysis* MTA::computeLocksets(TCT* tct)
{
    LockAnalysis* lsa = new LockAnalysis(tct);
    lsa->analyze();
    return lsa;
}

MHP* MTA::computeMHP(SVFModule* module)
{

    DBOUT(DGENERAL, outs() << pasMsg("MTA analysis\n"));
    DBOUT(DMTA, outs() << pasMsg("MTA analysis\n"));
    SVFIR* pag = PAG::getPAG();
    PointerAnalysis* pta = AndersenWaveDiff::createAndersenWaveDiff(pag);
    // pta->getPTACallGraph()->dump("ptacg");

    DBOUT(DGENERAL, outs() << pasMsg("Build TCT\n"));
    DBOUT(DMTA, outs() << pasMsg("Build TCT\n"));
    DOTIMESTAT(double tctStart = stat->getClk());
    tct = std::make_unique<TCT>(pta);
    tcg = tct->getThreadCallGraph();
    DOTIMESTAT(double tctEnd = stat->getClk());
    DOTIMESTAT(stat->TCTTime += (tctEnd - tctStart) / TIMEINTERVAL);

    if (pta->printStat())
    {
        stat->performThreadCallGraphStat(tcg);
        stat->performTCTStat(tct.get());
    }

    // tcg->dump("tcg");

    DBOUT(DGENERAL, outs() << pasMsg("MHP analysis\n"));
    DBOUT(DMTA, outs() << pasMsg("MHP analysis\n"));

    DOTIMESTAT(double mhpStart = stat->getClk());
    MHP* mhp = new MHP(tct.get());
    mhp->analyze();
    DOTIMESTAT(double mhpEnd = stat->getClk());
    DOTIMESTAT(stat->MHPTime += (mhpEnd - mhpStart) / TIMEINTERVAL);

    DBOUT(DGENERAL, outs() << pasMsg("MHP analysis finish\n"));
    DBOUT(DMTA, outs() << pasMsg("MHP analysis finish\n"));
    return mhp;
}

class UnionFind {
public:
    void makeSet(const NodeID var) {
        parent[var] = var;
    }

    NodeID find(const NodeID var) {
        if (parent[var] != var) {
            parent[var] = find(parent[var]); // Path compression
        }
        return parent[var];
    }

    void unite(const NodeID var1, const NodeID var2) {
        NodeID root1 = find(var1);
        NodeID root2 = find(var2);
        if (root1 != root2) {
            parent[root2] = root1;
        }
    }

private:
    Map<NodeID, NodeID> parent;
};

///*!
// * Check   (1) write-read race
// * 		 (2) write-write race (optional)
// * 		 (3) read-read race (optional)
// * when two memory access may-happen in parallel and are not protected by the same lock
// * (excluding global constraints because they are initialized before running the main function)
// */
void MTA::detect(SVFModule* module)
{

    DBOUT(DGENERAL, outs() << pasMsg("Starting Race Detection\n"));

    Set<const LoadStmt*> loads;
    Set<const StoreStmt*> stores;
    SVFIR* pag = SVFIR::getPAG();
    PointerAnalysis* pta = AndersenWaveDiff::createAndersenWaveDiff(pag);

    Set<const SVFInstruction*> needcheckinst;
    // Add symbols for all of the functions and the instructions in them.
    for (const SVFFunction* F : module->getFunctionSet())
    {
        // collect and create symbols inside the function body
        for (const SVFBasicBlock* svfbb : F->getBasicBlockList())
        {
            for (const SVFInstruction* svfInst : svfbb->getInstructionList())
            {
                for(const SVFStmt* stmt : pag->getSVFStmtList(pag->getICFG()->getICFGNode(svfInst)))
                {
                    if (const LoadStmt* l = SVFUtil::dyn_cast<LoadStmt>(stmt))
                    {
                        loads.insert(l);
                    }
                    else if (const StoreStmt* s = SVFUtil::dyn_cast<StoreStmt>(stmt))
                    {
                        stores.insert(s);
                    }
                }
            }
        }
    }

    // outs() << "# of loads / stores = " << loads.size() << ", " << stores.size() << "\n";

    Set<NodeID> allVarIDs;
    for (const auto* load : loads) 
        allVarIDs.insert(load->getRHSVarID());
    for (const auto* store : stores) 
        allVarIDs.insert(store->getLHSVarID());

    // outs() << "# of variables = " << allVarIDs.size() << "\n";

    // Initialize Union-Find data structure
    UnionFind uf;
    for (const NodeID var : allVarIDs) 
        uf.makeSet(var);

    Map<NodeID, std::vector<NodeID>> memLocToVars;

    for (NodeID varID : allVarIDs) 
    {
        const PointsTo& pts = pta->getPts(varID);
        for (NodeID memLoc : pts) 
            memLocToVars[memLoc].push_back(varID);
    }

    for (const auto& [memLoc, varList] : memLocToVars) 
    {
        if (varList.size() <= 1)
            continue;
        NodeID firstVar = varList[0];
        for (size_t i = 1; i < varList.size(); ++i) 
            uf.unite(firstVar, varList[i]);
    }

    // Group loads and stores by alias set
    Map<NodeID, std::vector<const LoadStmt*>> aliasSetToLoads;
    Map<NodeID, std::vector<const StoreStmt*>> aliasSetToStores;

    for (const auto* load : loads) 
    {
        NodeID varID = load->getRHSVarID();
        NodeID aliasSetID = uf.find(varID);
        aliasSetToLoads[aliasSetID].push_back(load);
    }

    for (const auto* store : stores) 
    {
        NodeID varID = store->getLHSVarID();
        NodeID aliasSetID = uf.find(varID);
        aliasSetToStores[aliasSetID].push_back(store);
    }

    const size_t INITIAL_BUFFER_SIZE = 200;
    std::string buffer;
    buffer.reserve(INITIAL_BUFFER_SIZE); // Choose an appropriate size
    const size_t BUFFER_LIMIT = 1 << 18; // 256kB limit
    // size_t set_id = 0;

    // Iterate over all alias sets
    for (const auto& [aliasSetID, loadVec] : aliasSetToLoads) 
    {
        auto storeIt = aliasSetToStores.find(aliasSetID);
        if (storeIt == aliasSetToStores.end())
            continue;

        const auto& storeVec = storeIt->second;

        // outs() << "processing alias set #" << ++set_id << ": " << loadVec.size() << ", " << storeVec.size() << "\n";
        
        // Todo: handle large groups
        if (loadVec.size() * storeVec.size() >= 10000)
            continue;

        for (const auto* load : loadVec) 
        {
            const SVFInstruction* loadInst = load->getInst();
            if (loadInst == nullptr)
                continue;

            for (const auto* store : storeVec) 
            {
                const SVFInstruction* storeInst = store->getInst();
                if (storeInst == nullptr)
                    continue;

                // Check for MHP and locks. Aliasing has been handled by UnionFind.
                if (mhp->mayHappenInParallelInst(loadInst, storeInst) &&
                    lsa->isProtectedByCommonLock(loadInst, storeInst) == false) 
                {

                    buffer.append(store->getValue()->getSourceLoc());
                    buffer.append(load->getValue()->getSourceLoc());
                    buffer.push_back('\n');

                    // Flush buffer if it exceeds the limit
                    if (buffer.size() >= BUFFER_LIMIT) 
                    {
                        outs() << buffer;
                        buffer.clear();
                    }
                }
            }
        }
    }
    if (!buffer.empty()) 
        outs() << buffer;
}

