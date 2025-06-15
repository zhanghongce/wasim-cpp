
#include "config/testpath.h"
#include "frontend/btor2_encoder.h"
#include "apps/pipe_bwd/conds.h"
#include "utils/misc.h"

#include <chrono>
#include <cassert>


using namespace wasim;
using namespace smt;


void ExamineModel(const smt::TermList & var_eq_val) {
  for (const auto & e : var_eq_val)
   std::cout << e->to_string() << std::endl;
}

void ExtractCex(SmtSolver & slv, const smt::Term & postc, smt::TermList & out, bool bit_level = false) {
  UnorderedTermSet vars;
  get_free_symbols(postc,vars);
  for (const auto & v : vars) {
    auto val = slv->get_value(v);
    if (bit_level) {
      unsigned width;
      if (val->get_sort()->get_sort_kind() == smt::SortKind::BV && ((width = val->get_sort()->get_width()) > 1)) {
        for (unsigned idx = 0; idx < width; ++idx) {
          out.push_back(slv->make_term(smt::Equal, 
            slv->make_term(smt::Op(smt::PrimOp::Extract,idx,idx),v), 
            slv->make_term(smt::Op(smt::PrimOp::Extract,idx,idx),val)));
        }
        continue;
      } // end if do it bit-by-bit
    } // even if bit-level, those width == 1, will use the following 
    out.push_back(slv->make_term(smt::Equal, v, val));
  } // end of to_reduced construction
}

// postc is the formula that is SAT
void ReduceCex(SmtSolver & slv, const smt::Term & postc, smt::TermList & var_eq_val) {
  auto not_postc = slv->make_term(smt::Not, postc); // \neg postc
  slv->push();
  auto res = reduce_unsat_core_to_fixedpoint(not_postc, var_eq_val, slv);
  assert(res); // must be unsat
  // we don't even need to push pop twice...
  assert(!var_eq_val.empty());
  reduce_unsat_core_linear(not_postc, var_eq_val, slv);
  slv->pop();
  assert(!var_eq_val.empty());
}

// `out` returns the condition on the pre-state that we need to comply, but actually not...
bool TransCheck(const Conds & c1, const TermVec & transcond, const Conds & c2, TermVec * out) {
  auto & solver = c1.s.get_solver();
  const auto & sts = c1.s;
  bool succ = true;

  
  TermVec c2_simplifed;
  {// first simplify c2
    // collect all assumptions
    TermVec asmpts_all = c1.conds;
    asmpts_all.insert(asmpts_all.end(), transcond.begin(), transcond.end());

    for (const auto & c : c2.conds) {
      // v -> v.next -> v.update_function
      auto next_a = solver->substitute( sts.next(c), sts.next_state_updates() );
      auto next_a_simplified = expr_simplify_ite(next_a, asmpts_all, solver );
      auto next_inputvars = get_semantically_contained_next_input_vars(next_a_simplified, asmpts_all, sts);
      TermVec next_inputvars_vec(next_inputvars.begin(), next_inputvars.end()); // set to vec
      auto quantified_a = UniversalQuantifierInstantiation(next_a_simplified, next_inputvars_vec, solver);
      c2_simplifed.push_back(quantified_a);
      if(quantified_a->to_string() == "#b0") { // this must be wrong!!!
        std::cout << " next_a := " << next_a->to_string() << std::endl;
        solver->push();
        solver->assert_formula(next_a);
        auto res = solver->check_sat_assuming(asmpts_all);
        assert(res.is_unsat());
        smt::UnorderedTermSet unsatcore;
        solver->get_unsat_assumptions(unsatcore);
        solver->pop();
        unsigned idx = 0;
        for (const auto & a : asmpts_all) {
          bool found = unsatcore.find(a) != unsatcore.end(); // in core
          std::cout << " A " << idx++ <<" := " << (found ? (a->to_string()): std::string(" n/a ")) << std::endl;
        }        
        std::cout << "--------------------------------------\n";
      }
    }
  }

  solver->push();
  for (const auto & a : c1.conds)
    solver->assert_formula(a);
  for (const auto & c : transcond)
    solver->assert_formula(c);

  unsigned c2_idx = 0;
  smt::TermList var_eq_val;
  smt::Term not_next_a_cached;

  for (const auto & next_a : c2_simplifed) {
    std::cout << "next a:" << next_a->to_string() << std::endl;
    auto not_next_a = solver->make_term(Not, next_a);
    auto res = solver->check_sat_assuming( {not_next_a} );
    if (!res.is_unsat()) {
      succ = false;
      if (out)
        out->push_back(next_a);
// ------- DEBUGGING --------
      std::cout << "[TransCheck] Fail idx: " << (c2_idx++) << std::endl;
      ExtractCex(solver, not_next_a, var_eq_val);
      not_next_a_cached = not_next_a;
      break;
// ------- END OF DEBUGGING --------
    } else
      std::cout << "[TransCheck] Ok idx: " << (c2_idx++) << std::endl;
  }
  solver->pop();

  if (not_next_a_cached) {
    assert(!var_eq_val.empty());
    ReduceCex(solver, not_next_a_cached, var_eq_val);
    ExamineModel(var_eq_val);
  }


  return succ;
}


int main() {


  SmtSolver solver = BoolectorSolverFactory::create(false);

  solver->set_logic("QF_UFBV");
  solver->set_opt("incremental", "true");
  solver->set_opt("produce-models", "true");
  solver->set_opt("produce-unsat-assumptions", "true");

  TransitionSystem sts(solver);
  BTOR2Encoder btor_parser("/home/hongcez/mingkai/piccolo/piccolo.btor2", sts);

  Conds LastState(sts);
  {
    auto inst = Sv("inst_reg_s3");
    auto rd = Sel( inst , 11, 7);
    auto rs1 = Sel( inst , 19, 15);
    auto rs2 = Sel( inst , 24, 20);
    LastState.add(Eq(Sv("s2_to_s3"), 1)); // 0 will fail
    LastState.add(Eq(Sv("gpr_regfile.write_rd_rd"), rd)); // 1 OK

    LastState.add(Eq(Sv("gpr_regfile.EN_write_rd"), 1)); // 2 will fail
    auto registers = Collect("gpr_regfile.regfile.arr","[","]");
    LastState.add( Eq(Sv("gpr_regfile.write_rd_rd_val"), Add(Read(registers,rs1), Read(registers, rs2)) ) ); // 3 will fail
  }
  LastState.print();
  LastState.simplify_inputvar_foreach_constraint({}); // try to simplify the inputvars

  // the following are true, this will explain s2_to_s3 is 0
  std::cout << "c1:" << LastState.check( Eq(Sv("s2_to_s3$D_IN"), 0), {Eq(Sv("rg_retiring$EN"), 0)} ) << "\n";
  std::cout << "c2:" << LastState.check( Eq(Sv("s2_to_s3$EN"), 1), {Eq(Sv("rg_retiring$EN"), 0)} ) << "\n";
  return 0;

  // LastState --> wb_ex == 0 --> LastState (get next state, simplify?)
  //  state union?
  // TransCheck(LastState, { Eq(Sv("s3_deq$EN"), 0), Eq(Sv("RST_N"), 1)}, LastState, NULL);
  // TransCheck(LastState, { Eq(Sv("s3_deq$D_IN"), 0), Eq(Sv("RST_N"), 1)}, LastState, NULL);
  TransCheck(LastState, { Eq(Sv("rg_retiring$EN"), 0), Eq(Sv("RST_N"), 1)}, LastState, NULL);
                              // 4                               5
  // TODO: you may need to add invariant-gen

#if 0
  // SecondLastState --> Eq(Sv("ex_go"), 1) -->  LastState

  std::cout << "--------Back to id_ex_regs ---------------\n" ;
  //    The assumptions here are over the pre-state
  auto IdExState = LastState.backward({Eq(Sv("ex_go"),1), Eq(Sv("rst"), 0)});

  IdExState.add(Eq(Sv("id_ex_valid"), 1));
  IdExState.add(Eq(Sv("id_ex_op"), 1));

  IdExState.simplify_using_mutual_asmpt(); // HZ there are input variables that you cannot avoid...
  IdExState.print();
  IdExState.add(Eq(Sel(Sv("id_ex_inst"),7,6), 1));

  // ex_go ==0 /\ rst == 0 |-> id_go == 0
  std::cout << "Check:"<< IdExState.check( Eq(Sv("id_go"), 0), { Eq(Sv("ex_go"), 0), Eq(Sv("rst"), 0)}  ) << std::endl;


  TermVec failed_constraints;
  // check if we start from pre-state with assumptions, are we guaranteed to end in a state satisfiying post-conditon
  TransCheck(IdExState, { Eq(Sv("ex_go"), 0), Eq(Sv("rst"), 0)}, IdExState, &failed_constraints);
  for (const auto & a : failed_constraints) {
    // TODO: remove the old one...
    std::cout << "[TransCheck] Failed to comply with: " << a->to_string() << std::endl;
    auto inputv = get_semantically_contained_next_input_vars(a, IdExState.conds, sts);
    for (const auto & v : inputv)
      std::cout << "Semantically depends on " << v->to_string() << std::endl;
  }

  auto IfIdState = IdExState.backward({Eq(Sv("id_go"),1), Eq(Sv("rst"), 0)});
  IfIdState.print();
  failed_constraints.clear();
  auto res = TransCheck(IfIdState, { Eq(Sv("id_go"), 0), Eq(Sv("rst"), 0)}, IfIdState, &failed_constraints);

  // check this property:
  //  (inst_valid && inst_ready) && (inst[7:6] == ADD) |-> (constraints in IfIdState)
  
  // TODO : semantically removing independent input vars

  // find the leaf that 
  // TODO: compute fixedpoint under { Eq(Sv("ex_go"), 0), Eq(Sv("rst"), 0)}
  // check that fixed point guarantees { Eq(Sv("ex_go"), 1), Eq(Sv("rst"), 0)}     LastState
  // auto IdExStateFixedpoint = IdExState.compute_fixedpoint({ Eq(Sv("ex_go"), 0), Eq(Sv("rst"), 0)});

  // TermVec failed_constraints2;
  // TransCheck(IdExStateFixedpoint,  { Eq(Sv("ex_go"), 1), Eq(Sv("rst"), 0)}, LastState, &failed_constraints2);
  // assert(failed_constraints2.empty());

  exit(1);
#endif

  return 0;
}


