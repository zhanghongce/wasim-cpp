#include <chrono>
#include "assert.h"
#include "config/testpath.h"
#include "frontend/btor2_encoder.h"
#include "framework/symsim.h"
#include "framework/ts.h"
#include "smt-switch/boolector_factory.h"

using namespace wasim;
using namespace smt;

int main() {


  SmtSolver solver = BoolectorSolverFactory::create(false);

  solver->set_logic("QF_UFBV");
  solver->set_opt("incremental", "true");
  solver->set_opt("produce-models", "true");
  solver->set_opt("produce-unsat-assumptions", "true");

  TransitionSystem sts(solver);
  BTOR2Encoder btor_parser("/home/hongcez/wenbin/symsim-design/piccolo/piccolo.btor2", sts);

  std::cout << sts.trans()->to_string() << std::endl;
  
  SymbolicSimulator sim(sts, solver);
  
  sim.init();

  auto inputmap = sim.convert( {{"RST_N", 1}} );

  for (int i = 0; i < 100; ++i) {
    sim.set_input(inputmap, {});
    std::cout << "step: " << i;
    std::cout.flush();
    sim.sim_one_step();
    std::cout << "\n";
  }


  return 0;
}


