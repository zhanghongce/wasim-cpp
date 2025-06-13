/*********************                                                        */
/*! \file
 ** \verbatim
 ** Top contributors (to current version):
 **   Hongce Zhang
 ** This file is part of the wasim-cpp project.
 ** Copyright (c) 2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file LICENSE in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief
 **
 **
 **/


 #include "modelchecking/prover.h"
 #include "modelchecking/ic3ng.h"

 namespace wasim
 {
  std::shared_ptr<Prover> make_prover(Engine e, 
        const smt::Term & p, const TransitionSystem & ts,
        const smt::SmtSolver & s,
        const smt::TermVec & assumptions,
        const PonoOptions & opt) {
    if (e == Engine::IC3NG_BITS) {
        return std::make_shared<IC3ng>(p, ts, s, assumptions, opt);
    } 
    throw SimulatorException("Unimplemented model checking engine!");
    // no use
    return nullptr;
  }
 } // namespace wasim

 
