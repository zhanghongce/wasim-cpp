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

#include <cassert>

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



// --------------------------------------------------------------------------------

bool reduce_unsat_core_to_fixedpoint(
  const smt::Term & formula,
  smt::TermList & core_inout,
  const smt::SmtSolver & reducer_) {
  // already pushed outside (because we want to disable all labels)
  reducer_->assert_formula(formula);

  // exit if the formula is unsat without assumptions.
  smt::Result r = reducer_->check_sat();
  if (r.is_unsat()) {
    core_inout.clear();
    return true;
  }

  bool first_round = true;
  while(true) {
    r = reducer_->check_sat_assuming_list(core_inout);
    if (r.is_sat()) {
      assert(first_round);
      return false;
    }
    first_round = false;

    smt::TermList core_out;
    reducer_->get_unsat_assumptions(core_out);
    if (core_inout.size() == core_out.size()) {
      return true; // fixed point is reached
    }
    assert(core_out.size() < core_inout.size());
    core_inout.swap(core_out);  // namely, core_inout = core_out,  but no need to copy
  }
  assert(false); // should not reach this point
  return true;
}

void reduce_unsat_core_to_fixedpoint(
  const smt::Term & formula, 
  smt::UnorderedTermSet & core_inout,
  const smt::SmtSolver & reducer_) {
  // already pushed outside (because we want to disable all labels)
  reducer_->assert_formula(formula);

  // exit if the formula is unsat without assumptions.
  smt::Result r = reducer_->check_sat();
  if (r.is_unsat()) {
    core_inout.clear();
    return;
  }

  while(true) {
    r = reducer_->check_sat_assuming_set(core_inout);
    assert(r.is_unsat());

    smt::UnorderedTermSet core_out;
    reducer_->get_unsat_assumptions(core_out);
    if (core_inout.size() == core_out.size()) {
      break; // fixed point is reached
    }
    assert(core_out.size() < core_inout.size());
    core_inout.swap(core_out);  // namely, core_inout = core_out,  but no need to copy
  }
} // reduce_unsat_core_to_fixedpoint


void remove_and_move_to_next(smt::TermList & pred_set, smt::TermList::iterator & pred_pos,
  const smt::UnorderedTermSet & unsatcore) {

  auto pred_iter = pred_set.begin(); // pred_pos;
  auto pred_pos_new = pred_set.begin();

  bool reached = false;
  bool next_pos_found = false;

  while( pred_iter != pred_set.end() ) {

    if (pred_iter == pred_pos) {
      assert (!reached);
      reached = true;
    }
    
    if (unsatcore.find(*pred_iter) == unsatcore.end()) {
      assert (reached);
      pred_iter = pred_set.erase(pred_iter);
    } else {
      if (reached && ! next_pos_found) {
        pred_pos_new = pred_iter;
        next_pos_found = true;
      }
      ++ pred_iter;
    }
  } // end of while

  assert(reached);
  if (! next_pos_found) {
    assert (pred_iter == pred_set.end());
    pred_pos_new = pred_iter;
  }
  pred_pos = pred_pos_new;
} // remove_and_move_to_next

void reduce_unsat_core_linear(
    const smt::Term & formula,
    smt::TermList & assumption_list,
    const smt::SmtSolver & reducer_) {
  
  // already pushed outside (because we want to disable all labels)
  reducer_->assert_formula(formula);

  // exit if the formula is unsat without assumptions.
  smt::Result r = reducer_->check_sat();
  if (r.is_unsat())
    return;

  r = reducer_->check_sat_assuming_list(assumption_list);
  assert(r.is_unsat());
  auto to_remove_pos = assumption_list.begin();

  while(to_remove_pos != assumption_list.end()) {
    smt::Term term_to_remove = *to_remove_pos;
    auto pos_after = assumption_list.erase(to_remove_pos);
    r = reducer_->check_sat_assuming_list(assumption_list);
    to_remove_pos = assumption_list.insert(pos_after, term_to_remove);
    
    if (r.is_sat()) {
      ++ to_remove_pos;
    } else { // if unsat, we can remove
      smt::UnorderedTermSet core_set;
      reducer_->get_unsat_assumptions(core_set);
      // below function will update assumption_list and to_remove_pos
      remove_and_move_to_next(assumption_list, to_remove_pos, core_set);
    }
  } // end of while
} // end of reduce_unsat_core_linear


// a helper function : the rev version
// it goes from the end to the beginning
void remove_and_move_to_next_rev(smt::TermList & pred_set, smt::TermList::iterator & pred_pos,
  const smt::UnorderedTermSet & unsatcore) {

  auto pred_iter = pred_set.end(); // pred_pos;
  auto pred_pos_new = pred_set.end();

  pred_pos_new--;

  bool reached = false;
  bool next_pos_found = false;

  while( pred_iter != pred_set.begin() ) {
    pred_iter--;
    
    if (!reached && pred_iter == pred_pos) {
      reached = true;
    }
    
    if (unsatcore.find(*pred_iter) == unsatcore.end()) {
      assert (reached);
      pred_iter = pred_set.erase(pred_iter);
    } else {
      if (reached && ! next_pos_found) {
        pred_pos_new = pred_iter;
        pred_pos_new ++;
        next_pos_found = true;
      }
    }
  } // end of while

  assert(reached);
  if (! next_pos_found) {
    assert (pred_iter == pred_set.begin());
    pred_pos_new = pred_iter;
  }
  pred_pos = pred_pos_new;
} // remove_and_move_to_next

void reduce_unsat_core_linear_rev(
    const smt::Term & formula,
    smt::TermList & assumption_list,
    const smt::SmtSolver & reducer_) {
  
  // already pushed outside (because we want to disable all labels)
  reducer_->assert_formula(formula);

  // exit if the formula is unsat without assumptions.
  smt::Result r = reducer_->check_sat();
  if (r.is_unsat()) {
    assumption_list.clear();
    return;
  }

  r = reducer_->check_sat_assuming_list(assumption_list);
  assert(r.is_unsat());

  auto to_remove_pos = assumption_list.end();

  while(to_remove_pos != assumption_list.begin()) {
    to_remove_pos--; // firstly, point to the last one
    smt::Term term_to_remove = *to_remove_pos;

    auto pos_after = assumption_list.erase(to_remove_pos);
    r = reducer_->check_sat_assuming_list(assumption_list);
    to_remove_pos = assumption_list.insert(pos_after, term_to_remove);
    
    if (r.is_sat()) {
      continue; // we cannot remove this, so move to the next (prior one)
    } else { // if unsat, we can remove
      smt::UnorderedTermSet core_set;
      reducer_->get_unsat_assumptions(core_set);
      // below function will update assumption_list and to_remove_pos
      remove_and_move_to_next_rev(assumption_list, to_remove_pos, core_set);
    }
  } // end of while
} // end of reduce_unsat_core_linear

  
} // namespace wasim


