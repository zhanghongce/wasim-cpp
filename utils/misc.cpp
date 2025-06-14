/*********************                                                        */
/*! \file
 ** \verbatim
 ** Top contributors (to current version):
 **   Hongce Zhang
 ** This file is part of the wasim project.
 ** Copyright (c) 2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file LICENSE in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief
 **
 **
 **/

#include "utils/misc.h"
#include "utils/exceptions.h"

namespace wasim
{


smt::Term bool_to_bv(const smt::Term & t, smt::SmtSolver & solver_) {
  if (t->get_sort()->get_sort_kind() == smt::BOOL) {
    smt::Sort bv1sort = solver_->make_sort(smt::BV, 1);
    return solver_->make_term(
        smt::Ite, t, solver_->make_term(1, bv1sort), solver_->make_term(0, bv1sort));
  } else {
    return t;
  }
}

smt::Term bv_to_bool(const smt::Term & t, smt::SmtSolver & solver_) {
  smt::Sort sort = t->get_sort();
  if (sort->get_sort_kind() == smt::BV) {
    if (sort->get_width() != 1) {
      throw SimulatorException("Can't convert non-width 1 bitvector to bool.");
    }
    return solver_->make_term(
        smt::Equal, t, solver_->make_term(1, solver_->make_sort(smt::BV, 1)));
  } else {
    return t;
  }  
}

  
} // namespace wasim


