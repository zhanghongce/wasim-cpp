#pragma once
// #include "assert.h"
// #include <string>
// #include <iomanip>
// #include <unordered_map>

#include "smt-switch/boolector_factory.h"
// #include "../deps/smt-switch/local/include/smt-switch/boolector_extensions.h"

#include "smt-switch/smt.h"
// #include "../deps/smt-switch/local/include/smt-switch/generic_sort.h"

// #include "../utils/exceptions.h"

#include "ts.h"
#include "symsim.h"
#include "symtraverse.h"

// #include <iostream>
// #include <unordered_map>
// #include <utility>
// #include <functional>
// #include <vector>
// #include <set>
#include <vector>
#include <iostream>
#include <iterator>
#include <algorithm>
#include <variant>

using namespace std;

namespace wasim
{

smt::TermVec tag2asmpt_c1(std::string flag, SymbolicExecutor& executor, smt::SmtSolver & solver);

void extend_branch_init(std::vector<std::vector<StateAsmpt>>& branch_list, SymbolicExecutor & executor, TransitionSystem & sts, std::vector<std::string> base_sv, std::string flag, std::vector<TraverseBranchingNode> order, smt::SmtSolver & solver);

void extend_branch_next_phase(std::vector<std::vector<StateAsmpt>>& branch_list, SymbolicExecutor & executor, TransitionSystem & sts, std::vector<std::string> base_sv, std::string flag, assignment_type phase_maker, std::vector<TraverseBranchingNode> order, smt::SmtSolver & solver);


void extend_branch_same_phase(std::vector<std::vector<StateAsmpt>>& branch_list, SymbolicExecutor & executor, TransitionSystem & sts, std::vector<std::string> base_sv, std::string flag, assignment_type phase_maker, std::vector<TraverseBranchingNode> order, smt::SmtSolver & solver);
}