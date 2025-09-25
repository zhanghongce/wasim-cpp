#pragma once

#include "apps/pipe_bwd/ops.h"
#include "framework/symsim.h"
#include "framework/state_simplify.h"
#include "framework/sygus_simplify.h"

namespace wasim {


struct Conds{
public:
  smt::TermVec conds;
  TransitionSystem & s;
  
  // map state -> state.nxt
  // and check `in` does not contain input.nxt/state.nxt
  smt::Term safe_nxt_substitute(const smt::Term &in) const ;

  // constructor
  Conds(TransitionSystem & sts) : s(sts) {}

  // add a condition to the list of conditions
  void add(const smt::Term & t) {conds.push_back(t);}

  // compute the pre-image of the conditions
  // the assumptions are considered as the pre-state
  // the pre-image is computed by substituting the next state variables
  // with the current state variables, and then simplifying the expression
  // using the assumptions
  // the result is a new Conds object with the pre-image conditions
  Conds backward(const smt::TermVec & assumptions) const;


public:
  void simplify_using_mutual_asmpt() {
    simplify_using_mutual_asmpt(conds);
  }

protected:
  // ----------------------------------------------------------------------------
  // this should not be called outside, please use the one without arguments (the one above)
  // this function simplifies all asmpts, when processing c, it uses all conds other than c
  // will change asmpts in place
  void simplify_using_mutual_asmpt(smt::TermVec & asmpts);

public:
  // ----------------------------------------------------------------------------
  // for each constraint, try to simplify its inputs, under assumptions asmpt
  void simplify_inputvar_foreach_constraint(const smt::TermVec & asmpt);
  // check if conds contain any input / input.nxt (syntactically/semantically)
  bool check_contains_inputvar() const;

  bool syntactically_contains_input_vars() const ;
  smt::UnorderedTermSet get_syntactically_contained_input_vars() const ;
  smt::UnorderedTermSet get_semantically_contained_input_vars() const ;
  smt::UnorderedTermSet get_syntactically_contained_next_input_vars() const ;
  smt::UnorderedTermSet get_semantically_contained_next_input_vars() const ;
  // check if t is valid under conds /\ assumptions
  bool check(const smt::Term & t, const smt::TermVec & assumptions);

  // ----------------------------------------------------------------------------
  void print() const;
  void write_to_file(const std::string & fname) const;
  void read_from_file(const std::string & fname);

  static void write_termvec_to_file(const std::string & fname, const smt::TermVec & tvec);
  static void read_termvec_from_file(const std::string & fname, smt::TermVec & tvec, smt::SmtSolver & slv);

}; // Conditions



} // namespace wasim
