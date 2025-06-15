#pragma once

#include "smt-switch/smt.h"

namespace wasim {
// some useful utilities

  smt::Term bool_to_bv(const smt::Term & t, smt::SmtSolver & solver_);

  smt::Term bv_to_bool(const smt::Term & t, smt::SmtSolver & solver_);


  // will be used in replacement of unsatcore reducer
  void reduce_unsat_core_to_fixedpoint(const smt::Term & formula, smt::UnorderedTermSet & core_inout, const smt::SmtSolver & solver_);
  void reduce_unsat_core_linear(const smt::Term & formula, smt::TermList & assumption_list, const smt::SmtSolver & solver_);

  // return true, if succeed
  // return false, if it is not unsat
  bool reduce_unsat_core_to_fixedpoint(const smt::Term & formula, smt::TermList & core_inout, const smt::SmtSolver & solver_);
  // The rev version assumes that assumption_list are ordered as following:
  // [keep...remove]  (those we want to keep are put the first)
  void reduce_unsat_core_linear_rev(const smt::Term & formula, smt::TermList & assumption_list, const smt::SmtSolver & solver_);

  
}
