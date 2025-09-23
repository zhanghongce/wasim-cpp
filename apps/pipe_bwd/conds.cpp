#include "apps/pipe_bwd/conds.h"
#include "utils/container_shortcut.h"
#include "utils/misc.h"
#include "frontend/smt_in.h"


namespace wasim {

smt::Term Conds::safe_nxt_substitute(const smt::Term &in) const {
  smt::UnorderedTermSet vars;
  smt::get_free_symbols(in, vars);
  for (const auto & v : vars) {
    // we need to make sure that we don't have next state variables
    if (s.is_next_var(v)) // here it used to check just the input vars
      throw SimulatorException("Cannot safely map " + v->to_string() + " to next.");
  }
  return s.next(in);
} // end of safe_nxt_substitute


// compute the pre-image of the conditions
// the assumptions are considered as the pre-state
// the pre-image is computed by substituting the next state variables
// with the current state variables, and then simplifying the expression
// using the assumptions
// the result is a new Conds object with the pre-image conditions
Conds Conds::backward(const smt::TermVec & assumptions) const {
  // make assumptions finer-grain
  smt::TermVec parted_asmpts;
  for (const auto & a : assumptions)
    smt::conjunctive_partition(a, parted_asmpts, true);

  std::cout << "[backward] pre-check:" << std::endl;
  check_contains_inputvar();

  Conds ret(s);
  smt::TermVec & nvec = ret.conds;
  const auto & vmap = s.state_updates();
  auto & solver = s.get_solver();
  for (const auto & c : conds) {
    // Do NOT use this: auto nexpr = solver->AbsSmtSolver::substitute(c, vmap);
    // because we want to make sure the inputs are carefully handled
    // and it should contain no next state variables either
    auto nexpr = solver->AbsSmtSolver::substitute( safe_nxt_substitute(c), s.next_state_updates() );
    
    // assumptions are applied on the pre-image
    nexpr = expr_simplify_ite(nexpr, parted_asmpts, solver);
    // conjunction participation
    smt::TermVec parted;
    smt::conjunctive_partition(nexpr, parted, true);

    // todo: add xxx == 0 --> replace ...
    for (const auto & e : parted)
      nvec.push_back(e);
  } // for each cond in 

  ret.simplify_using_mutual_asmpt(ret.conds);

  // a check, which could be removed later
  for (const auto & c : ret.conds) {
    auto s = c->to_string();
    if (s.find("BTOR_") != string::npos)
      throw SimulatorException("We should not have any variable containing BTOR_");
  }

  // TODO : you may want to distruct bvand and and
  ret.simplify_inputvar_foreach_constraint(parted_asmpts);

  std::cout << "[backward] post-check:" << std::endl;
  ret.check_contains_inputvar();

  return ret;
} // end of backwards


// this function simplifies all asmpts, when processing c, it uses all conds other than c
// will change asmpts in place
void Conds::simplify_using_mutual_asmpt(smt::TermVec & asmpts) {
  auto & solver = s.get_solver();
  for (auto it = asmpts.begin(); it != asmpts.end();  ++it) {
    smt::TermVec conds_wo_c;
    for (auto copy_it = asmpts.begin(); copy_it != asmpts.end();  ++copy_it) {
      if (copy_it != it)
        conds_wo_c.push_back(*copy_it);
    } // end of copy
    *it = expr_simplify_ite(*it, conds_wo_c, solver);
  }
  // remove trivial ones
  for (auto it = asmpts.begin(); it != asmpts.end(); ) {
    if ( (*it)->is_value() ) {
      auto val = (*it)->to_string();
      if (val == "#b1" || val == "true" || val == "#t" || val == "(_ bv1 1)") {
        it = asmpts.erase(it);
        std::cout << "[simplify] remove constant true" << std::endl;
        continue;
      }
      if (val == "#b0" || val == "false" || val == "#f" || val == "(_ bv0 1)")
       throw SimulatorException("the condition cannot be satisfied!");
    } // end of check
    ++it;
  }
} // end of simplify_using_mutual_asmpt


// for each constraint, try to simplify its inputs, under assumptions asmpt
void Conds::simplify_inputvar_foreach_constraint(const smt::TermVec & asmpt) {

  for (const auto & c : asmpt) {
    std::cout << "C>>> " << c->to_string() << std::endl;
  }

  auto & solver = s.get_solver();
  for (auto & c : conds) {
    // for each c in conds, check if any variable in c can be removed
    // all_asmpt := asmpt U ( conds - {c} )
    smt::TermVec all_asmpt(asmpt);
    for (const auto & c_rest : conds) {
      if (c_rest != c) 
        all_asmpt.push_back(c_rest); // note here, after prior simplification, later onces will change as well
    }
    simplify_using_mutual_asmpt(all_asmpt);
    
    smt::UnorderedTermSet vars;
    smt::get_free_symbols(c,vars);
    // TODO: you may want to replace for all ...
    unsigned round = 0;
    bool need_to_remove = true;
    while(need_to_remove) {
      // for each var remove it
      need_to_remove = false;
      for (const auto & v : vars)
        if(s.is_input_var(v)) {
          // check if `c` is independent of `v` under `all_asmpt`
          if (e_is_independent_of_v(c, v, all_asmpt)) {
            need_to_remove = true; // remember to do next round
            std::cout << "[simplify_input] try to remove: " << v->to_string() << std::endl;
            std::cout << "[simplify_input] in: " << c->to_string() << std::endl;
            // now we should simplify
            c = remove_independent_var(c, v, all_asmpt, solver);

            {  // make sure the variable is indeed removed by function `remove_independent_var`
               // sometimes the prior function may fail to derive an expression without `v`
               // because of lacking of good rewriting strategies
              smt::UnorderedTermSet tmp_varset;
              smt::get_free_symbols(c, tmp_varset);
              if (tmp_varset.find(v) != tmp_varset.end()) {
                std::cout << "[DEBUG] "  << c->to_string() << std::endl;
                throw SimulatorException("ERROR: not removed: var " + v->to_string());
              }
            } // end of sanity check : var is removed

            { // a sanity check, make sure we don't accidentally create new vars
              auto s = c->to_string();
              if (s.find("BTOR_") != string::npos) {
                throw SimulatorException("c should not contain variables with BTOR_**");
              }
            }
          } // end of if removeable
      } // end of for each var
      if (round >= 1 && need_to_remove) {
        // if we going next round
        std::cout << "[simplify_input] round: " << round << std::endl;
      }
      // sometimes, when you removed 'v1' another 'v2' may become removeable
      // so if we have removed something, we recheck in the next round
      // if more can be removed.
      vars.clear();
      smt::get_free_symbols(c, vars);
      ++ round;
    } // end of while vars unchanged, if nothing is removeable in this round, will stop
  } // end of for each c in conds
} // simplify_inputvar_foreach_constraint


// check if conds contain any input / input.nxt (syntactically/semantically)
bool Conds::check_contains_inputvar() const {
  auto varset = get_syntactically_contained_input_vars();
  auto actual_varset = get_semantically_contained_input_vars();
  for (const auto & v : varset) {
    bool reduced = (actual_varset.find(v) == actual_varset.end());
    std::cout <<"[check] WARNING! structurally contains inputvar:" << v->to_string() 
              << (reduced ?  " (reducible)." : " *not* reducible")
              << std::endl;
  }
  bool noinputv = varset.empty();

  varset = get_syntactically_contained_next_input_vars();
  actual_varset = get_semantically_contained_next_input_vars();
  for (const auto & v : varset) {
    bool reduced = (actual_varset.find(v) == actual_varset.end());
    std::cout <<"[check] ERROR! structurally contains *next* inputvar:" << v->to_string() 
              << (reduced ?  " (reducible)." : " *not* reducible")
              << std::endl;
  }

  return (noinputv && varset.empty());
} // end of check_contains_inputvar


bool Conds::syntactically_contains_input_vars() const {
  for (const auto & c : conds) {
    smt::UnorderedTermSet vars;
    get_free_symbols(c,vars);
    for (const auto & v : vars)
      if(s.is_input_var(v))
        return true;
  }
  return false;
}

smt::UnorderedTermSet Conds::get_syntactically_contained_input_vars() const {
  smt::UnorderedTermSet inputvars;
  for (const auto & c : conds) {
    smt::UnorderedTermSet vars;
    get_free_symbols(c,vars);
    for (const auto & v : vars)
      if(s.is_input_var(v))
        inputvars.insert(v);
  }
  return inputvars;
}

smt::UnorderedTermSet Conds::get_semantically_contained_input_vars() const {
  smt::UnorderedTermSet remaining_vars;
  for (const auto & c : conds) {
    smt::UnorderedTermSet vars;
    get_free_symbols(c,vars);
    
    smt::TermVec conds_wo_c;
    for (const auto & other_c : conds)
      if(other_c != c)
        conds_wo_c.push_back(other_c);

    for (const auto & v : vars)
      if(s.is_input_var(v)) {
        if (!e_is_independent_of_v(c, v, conds_wo_c)) {
          remaining_vars.insert(v);
          std::cout << "[semantically contain input] "<< v->to_string() << std::endl;
        }
      }
  }
  return remaining_vars;
}

smt::UnorderedTermSet Conds::get_syntactically_contained_next_input_vars() const {
  smt::UnorderedTermSet nxt_inputvars;
  for (const auto & c : conds) {
    smt::UnorderedTermSet vars;
    get_free_symbols(c,vars);
    for (const auto & v : vars)
      if(s.is_next_input_var(v))
        nxt_inputvars.insert(v);
  }
  return nxt_inputvars;
}


smt::UnorderedTermSet Conds::get_semantically_contained_next_input_vars() const {
  smt::UnorderedTermSet remaining_vars;
  for (const auto & c : conds) {
    smt::UnorderedTermSet vars;
    get_free_symbols(c,vars);
    
    smt::TermVec conds_wo_c;
    for (const auto & other_c : conds)
      if(other_c != c)
        conds_wo_c.push_back(other_c);

    for (const auto & v : vars)
      if(s.is_next_input_var(v)) {
        if (!e_is_independent_of_v(c, v, conds_wo_c))
          remaining_vars.insert(v);
        std::cout << "[syntactically contain next input] "<< v->to_string() << std::endl;
      }
  }
  return remaining_vars;
}

// check if t is valid under conds /\ assumptions
bool Conds::check(const smt::Term & t, const smt::TermVec & assumptions) {
  auto & solver = s.get_solver();
  solver->push();
  for (const auto & a: conds)
    solver->assert_formula(a);
  for (const auto & a: assumptions)
    solver->assert_formula(a);
  solver->assert_formula(solver->make_term(smt::Not, t));
  auto res = solver->check_sat();
  solver->pop();
  return res.is_unsat();
}

void Conds::print() const {
  for (const auto & c : conds) {
    std::cout << " #### " << c->to_string() << std::endl;
  }
}

void Conds::write_termvec_to_file(const std::string & fname, const smt::TermVec & tvec) {
  std::ofstream fout(fname);
  if (!fout.is_open())
    throw SimulatorException("Unable to write to " + fname);

  fout << tvec.size() << std::endl; // first the number of expressions
  size_t cnt = 0;
  // let's use cvc5, because boolector does not distinguish bool/bv1
  auto cvc_slv = smt::Cvc5SolverFactory::create(false);
  auto cvc_trans = smt::TermTranslator(cvc_slv);

  for (const auto & c_orig : tvec) {
    auto c = bv_to_bool(cvc_trans.transfer_term(c_orig), cvc_slv);

    smt::UnorderedTermSet free_vars;
    smt::get_free_symbols(c, free_vars);

    fout << "(define-fun cond" << cnt++ <<" (";
    std::vector<std::string> argstr;
    for (const auto & arg : free_vars)
      argstr.push_back("(" + arg->to_string() + " " + arg->get_sort()->to_string() + ")");
    fout << Join(argstr, " ") << ") " << c->get_sort()->to_string() << " ";
    fout << c->to_string() << ")\n";  
  } // end for each conds
}

void Conds::read_termvec_from_file(const std::string & fname, smt::TermVec & tvec, smt::SmtSolver & slv) {
  std::ifstream fin(fname);
  if (!fin.is_open())
    throw SimulatorException("Unable to read from " + fname);
  unsigned cnt;
  fin >> cnt;
  for (unsigned idx = 0; idx < cnt; ++idx) {
    std::string temp_file = "temp_sv.log";

    { // move next line to temp_file
      std::string linedata;
      while(linedata.empty())
        getline(fin, linedata);
      std::ofstream temp(temp_file);
      if (!temp.is_open())
        throw SimulatorException("unable to open temporary file for write " + temp_file); 
      temp << linedata << endl;
    }

    auto c = load_smt_fundef(temp_file, slv);
    if (c == nullptr)
      throw SimulatorException("Failure in parsing");
    tvec.push_back(c);
  } // for each cond

}

void Conds::write_to_file(const std::string & fname) const {
  write_termvec_to_file(fname, conds);
}

void Conds::read_from_file(const std::string & fname) {
  read_termvec_from_file(fname, conds, s.get_solver());
}


} // namespace wasim

