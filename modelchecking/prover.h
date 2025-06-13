/*********************                                                        */
/*! \file
 ** \verbatim
 ** Top contributors (to current version):
 **   Makai Mann, Ahmed Irfan, Florian Lonsing
 ** This file is part of the pono project.
 ** Copyright (c) 2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file LICENSE in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief
 **
 **
 **/

#pragma once

#include "modelchecking/proverresult.h"
#include "modelchecking/options.h"
#include "modelchecking/unroller.h"
#include "framework/ts.h"
#include "smt-switch/smt.h"

namespace wasim {

class Prover
{
 public:
  Prover(const smt::Term & p,  const smt::TermVec & assumptions,
         const TransitionSystem & ts,
         const smt::SmtSolver & s, PonoOptions opt);

  virtual ~Prover();

  virtual void initialize();

  virtual ProverResult prove();

  virtual ProverResult check_until(int k) = 0;

  virtual bool witness(std::vector<smt::UnorderedTermMap> & out) { return false; }

  /** Returns length of the witness
   *  this can be cheaper than actually computing the witness
   *  by default returns reached_k_+1, because reached_k_ was the
   *  last step that completed without finding a bug
   *  but some algorithms such as IC3 might need to follow the trace
   */
  virtual size_t witness_length() const;

  /** Gives a term representing an inductive invariant over current state
   * variables. Only valid if the property has been proven true. Only supported
   * by some engines
   */
  smt::Term invar();

 protected:
  /** Default implementation for computing a witness
   *  Assumes that this engine is unrolling-based and that the solver
   *   state is currently satisfiable with a counterexample trace
   *  populates witness_
   *  @return true on success
   */
  bool compute_witness() { return false; }

  bool initialized_;

  smt::SmtSolver solver_;

  smt::Term property_; ///< original property before copied to new solver
  smt::TermVec assumptions_;
  const TransitionSystem & ts_;

  Unroller unroller_;

  int reached_k_;  ///< the last bound reached with no counterexamples

  smt::Term bad_;

  PonoOptions options_;
  
  // NOTE: both witness_ and invar_ use terms from the engine's solver

  std::vector<smt::UnorderedTermMap> witness_; ///< populated by a witness if a CEX is found

  smt::Term invar_; ///< populated with an invariant if the engine supports it

};

std::shared_ptr<Prover> make_prover(Engine e, 
            const smt::Term & p, const TransitionSystem & ts,
            const smt::SmtSolver & s,
            const smt::TermVec & assumptions,
            const PonoOptions & opt);

}  // namespace pono
