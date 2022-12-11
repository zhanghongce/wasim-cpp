#include "term_manip.h"

namespace wasim {

// smt::TermVec args(const smt::Term & term){
//     smt::TermVec arg_vec;
//     for(auto pos = term->begin(); pos != term->end(); ++pos)
//         arg_vec.push_back(*pos);

//     return arg_vec;
// }

// smt::UnorderedTermSet get_free_variables(const smt::Term & term){
//     smt::UnorderedTermSet free_var;
//     smt::TermVec search_stack;
//     if(term->is_symbol()){
//         free_var.insert(term);
//     }
//     else{ // DFS
//         search_stack.push_back(term);
//         while (search_stack.size() != 0)
//         {
//             auto node = search_stack.back();
//             search_stack.pop_back();
//             if(node->is_symbol()){ // check
//                 free_var.insert(node);
//             }
//             auto children_vec = args(node);
//             std::reverse(std::begin(children_vec), std::end(children_vec));
//             search_stack.insert(search_stack.end(), children_vec.begin(),
//             children_vec.end());
//         }

//     }
//     return free_var;
// }

smt::Term free_make_symbol(const std::string & n,
                           smt::Sort symb_sort,
                           std::unordered_map<std::string, int> & name_cnt,
                           smt::SmtSolver & solver)
{
  int cnt;
  if (name_cnt.find(n) == name_cnt.end())
    cnt = 0;
  else
    cnt = name_cnt[n];

  do {
    ++cnt;
    name_cnt[n] = cnt;
    smt::Term symb;
    try {
      symb = solver->make_symbol(n + std::to_string(cnt), symb_sort);
      return symb;
    }
    catch (const std::exception & e) {  // maybe name conflict
      // std::cout << "New symbol: " << n + std::to_string(cnt) << " failed." <<
      // std::endl;
    }
  } while (true);
}

PropertyInterface::PropertyInterface(const std::string & filename,
                                     smt::SmtSolver & solver)
    : super(solver), filename_(filename), solver_(solver)
{
  set_logic_all();
  int res = parse(filename_);
  assert(!res);  // 0 means success
}

smt::Term PropertyInterface::register_arg(const std::string & name,
                                          const smt::Sort & sort)
{
  smt::Term tmpvar;
  try {
    tmpvar = solver_->get_symbol(name);
  }
  catch (const std::exception & e) {
    // cout << "ERROR: Could not find " << name << " in solver! Wrong input
    // value."<< endl; cout << sort->get_sort_kind() << endl;
    tmpvar = solver_->make_symbol(name, sort);
  }
  arg_param_map_.add_mapping(name, tmpvar);
  return tmpvar;  // we expect to get the term in the transition system.

  // TODO: symbolic values do not exist in the transition system
}

smt::Term PropertyInterface::return_defs()
{
  for (const auto & d : defs_) {
    // cout << d.first << " : " << d.second << endl;
    return d.second;
  }
}

void StateRW::write_term(const std::string & outfile, const smt::Term & expr)
{
  auto free_value_var = get_free_variables(expr);
  std::ofstream f;
  f.open(outfile.c_str(), ios::out | ios::app);
  auto line_start = "(define-fun FunNew (";
  auto line_end = ")";
  auto expr_sort = expr->get_sort()->to_string();
  auto expr_name = expr->to_string();
  auto v_sort = expr->get_sort()->to_string();
  // cout << expr->to_string() << endl;
  f << line_start;
  for (const auto & v : free_value_var) {
    f << "(" + v->to_string() + " " + v_sort + ") ";
  }
  f << line_end;
  f << " " + expr_sort + " ";
  f << expr_name + line_end << endl;
}

void StateRW::write_single_term(const std::string & outfile, const smt::Term & expr)
{
  std::ofstream f;
  f.open(outfile.c_str(), ios::out | ios::app);
  auto line_start = "(define-fun FunNew (";
  auto line_end = ")";
  auto expr_sort = expr->get_sort()->to_string();
  auto expr_name = expr->to_string();
  if (is_bv_const(expr)) {
    f << expr_name << endl;
  } else {
    f << line_start;
    f << "(" + expr_name + " " + expr_sort + ")";
    f << line_end;
    f << " " + expr_sort + " ";
    f << "(ite (= #b1 #b1) " + expr_name + " " + expr_name + ")" + line_end
      << endl;
  }
}

void StateRW::write_string(const std::string & outfile, const std::string & asmpt_interp)
{
  std::ofstream f;
  f.open(outfile.c_str(), ios::out | ios::app);
  f << asmpt_interp << endl;
}

bool StateRW::is_bv_const(const smt::Term & expr)
{
  if (expr->get_sort()->get_sort_kind() == smt::BOOL) {
    return true;
  } else if (expr->get_sort()->get_sort_kind() == smt::BV) {
    if (expr->is_value()) {
      return true;
    } else {
      return false;
    }
  } else {
    return false;
  }
}

smt::Term StateRW::str2bvnum(const std::string & int_num)
{
  auto str_num = int_num.substr(2);
  int bitwidth = static_cast<int>(str_num.size());
  int ret_dex = 0;
  for (int i = 0; i < str_num.size(); ++i) {
    if (str_num.at(i) == '1') {
      ret_dex += pow(2.0, bitwidth - i - 1);
    }
  }
  auto ret_term =
      solver_->make_term(ret_dex, solver_->make_sort(smt::BV, bitwidth));

  return ret_term;
}

void StateRW::StateWrite(const wasim::StateAsmpt & state,
                         const std::string & outfile_sv,
                         const std::string & outfile_asmpt)
{
  // 1. write state variables and expressions to outfile_sv
  for (auto sv : state.sv_) {
    // 1.1 for variable (LHS)
    auto var = sv.first;
    write_single_term(outfile_sv, var);

    // 1.2 for value expression (RHs)
    auto value = sv.second;
    auto free_value_var = get_free_variables(value);
    if (is_bv_const(value)) {
      write_single_term(outfile_sv, value);
    } else if ((free_value_var.size() == 1) && (value->get_op().is_null())) {
      write_single_term(outfile_sv, value);
    } else {
      write_term(outfile_sv, value);
    }
  }
  // 2. write assumptions and interpretations to outfile_asmpt
  for (int i = 0; i < state.asmpt_.size(); i++) {
    auto asmpt = state.asmpt_.at(i);
    auto free_asmpt_var = get_free_variables(asmpt);
    if (is_bv_const(asmpt)) {
      write_single_term(outfile_asmpt, asmpt);
    } else if ((free_asmpt_var.size() == 1) && (asmpt->get_op().is_null())) {
      write_single_term(outfile_asmpt, asmpt);
    } else {
      write_term(outfile_asmpt, asmpt);
    }

    auto asmpt_interp = state.assumption_interp_.at(i);
    write_string(outfile_asmpt, asmpt_interp);
  }
}

StateAsmpt StateRW::StateRead(const std::string & infile_sv, const std::string & infile_asmpt)
{
  // 1. read sv
  std::ifstream f(infile_sv.c_str());
  std::string temp_file = "temp_sv.log";
  std::string linedata = "";
  smt::Term input_term;
  smt::TermVec var_vec = {};
  smt::TermVec value_vec = {};
  smt::UnorderedTermMap state_sv = {};
  bool even_sv = false;
  while (f) {
    getline(f, linedata);
    if (f.fail()) {
      break;
    }
    std::ofstream temp;
    temp.open(temp_file.c_str(), ios::out);
    temp << linedata << endl;
    if (std::regex_match(linedata, regex("#b(\\d+)"))) {
      input_term = str2bvnum(linedata);
    } else {
      PropertyInterface pi(temp_file, solver_);
      input_term = pi.return_defs();
    }

    // cout << input_term->to_string() << endl;

    /// check the parity of cnt
    /// cnt is odd -> this input_term is sv (LHS)
    /// cnt is even -> this input_term is value (RHS)
    if (!even_sv) {
      var_vec.push_back(input_term);
    } else {
      value_vec.push_back(input_term);
    }
    even_sv = !even_sv;
  }
  f.close();
  int rm_sv;
  rm_sv = remove(temp_file.c_str());

  // finish read sv, then combine the two vectors to a map
  // cout << var_vec.size() << value_vec.size() << endl;
  assert(var_vec.size() == value_vec.size());
  for (int i = 0; i < var_vec.size(); i++) {
    auto key = var_vec.at(i);
    auto value = value_vec.at(i);
    state_sv[key] = value;
  }

  // 2. read asmpt
  std::ifstream f_asmpt(infile_asmpt.c_str());
  std::string temp_file_asmpt = "temp_asmpt.log";
  std::string linedata_asmpt = "";
  smt::Term input_asmpt;
  smt::TermVec state_asmpt_vec;
  std::vector<std::string> state_asmpt_interp_vec;
  bool even_asmpt = false;
  while (f_asmpt) {
    getline(f_asmpt, linedata_asmpt);
    if (f_asmpt.fail()) {
      break;
    }
    std::ofstream temp_asmpt;
    temp_asmpt.open(temp_file_asmpt.c_str(), ios::out);
    temp_asmpt << linedata_asmpt << endl;
    if (!even_asmpt) {
      if (std::regex_match(linedata_asmpt, regex("#b(\\d+)"))) {
        input_asmpt = str2bvnum(linedata_asmpt);
      } else {
        PropertyInterface pi(temp_file_asmpt, solver_);
        input_asmpt = pi.return_defs();
      }
      state_asmpt_vec.push_back(input_asmpt);
    } else {
      state_asmpt_interp_vec.push_back(linedata_asmpt);
    }
    even_asmpt = !even_asmpt;
  }

  f_asmpt.close();
  // cout << state_asmpt_vec.size() << " ->- " << state_asmpt_interp_vec.size()
  // << endl;
  // 3. build a new state
  int rm_asmpt;
  rm_asmpt = remove(temp_file_asmpt.c_str());
  StateAsmpt state_ret(state_sv, state_asmpt_vec, state_asmpt_interp_vec);
  return state_ret;
}

void StateRW::StateWriteTree(const std::vector<std::vector<StateAsmpt>> & branch_list,
                             const std::string & out_dir)
{
  for (int i = 0; i < branch_list.size(); i++) {
    auto state_list = branch_list.at(i);
    for (int j = 0; j < state_list.size(); j++) {
      auto state = state_list.at(j);
      std::string outfile_sv =
          out_dir + "state_sv_" + to_string(i) + "_" + to_string(j);
      std::string outfile_asmpt =
          out_dir + "state_asmpt_" + to_string(i) + "_" + to_string(j);
      StateWrite(state, outfile_sv, outfile_asmpt);
      // cout << "i = " << to_string(i) << ", j = " << to_string(j) << endl;
      // cout << outfile_sv << endl;
    }
  }
}

std::vector<std::vector<StateAsmpt>> StateRW::StateReadTree(const std::string & in_dir,
                                                            int num_i,
                                                            int num_j)
{
  cout << "Reading files. Please wait for seconds." << endl;
  std::vector<std::vector<StateAsmpt>> branch_list = {};
  for (int i = 0; i < num_i; i++) {
    std::vector<StateAsmpt> state_list = {};
    for (int j = 0; j < num_j; j++) {
      std::string infile_sv =
          in_dir + "state_sv_" + to_string(i) + "_" + to_string(j);
      std::string infile_asmpt =
          in_dir + "state_asmpt_" + to_string(i) + "_" + to_string(j);
      // std::string infile_asmpt = "";
      auto state = StateRead(infile_sv, infile_asmpt);
      state_list.push_back(state);

      // cout << "i = " << i << ", j = " << j << endl;
      // cout << infile_sv << endl;
    }
    branch_list.push_back(state_list);
  }
  cout << "Reading complete!" << endl;

  return branch_list;
}

smt::Term TermTransfer(const smt::Term & expr,
                       smt::SmtSolver & solver_old,
                       smt::SmtSolver & solver_new)
{
  smt::TermTranslator tt(solver_new);
  auto expr_new = tt.transfer_term(expr);

  return expr_new;
}

StateAsmpt StateTransfer(const wasim::StateAsmpt & state,
                         smt::SmtSolver & solver_old,
                         smt::SmtSolver & solver_new)
{
  smt::UnorderedTermMap sv_new;
  smt::TermVec asmpt_vec_new;
  for (const auto & sv : state.sv_) {
    auto var = sv.first;
    auto value = sv.second;

    auto var_new = TermTransfer(var, solver_old, solver_new);
    auto value_new = TermTransfer(value, solver_old, solver_new);
    sv_new.emplace(var_new, value_new);
  }

  for (const auto & asmpt : state.asmpt_) {
    auto asmpt_new = TermTransfer(asmpt, solver_old, solver_new);
    smt::Term asmpt_expr;
    if (asmpt_new->get_sort()->get_sort_kind() == smt::BV) {
      // convert bitvector 1 term to boolean term
      auto bvs = solver_new->make_sort(smt::BV, 1);
      smt::TermVec ite_term = {
        solver_new->make_term(
            smt::Equal, asmpt_new, solver_new->make_term(1, bvs)),
        solver_new->make_term(1),
        solver_new->make_term(0)
      };
      auto asmpt_temp = solver_new->make_term(smt::Ite, ite_term);
      asmpt_expr = asmpt_temp;
    } else {
      asmpt_expr = asmpt_new;
    }

    asmpt_vec_new.push_back(asmpt_expr);
  }

  StateAsmpt state_ret(sv_new, asmpt_vec_new, state.assumption_interp_);

  return state_ret;
}

smt::UnorderedTermSet SetTransfer(const smt::UnorderedTermSet & expr_set,
                                  smt::SmtSolver & solver_old,
                                  smt::SmtSolver & solver_new)
{
  smt::UnorderedTermSet expr_set_new;
  for (const auto & expr : expr_set) {
    auto expr_new = TermTransfer(expr, solver_old, solver_new);
    expr_set_new.insert(expr_new);
  }
  assert(expr_set.size() == expr_set_new.size());
  return expr_set_new;
}

smt::TermVec one_hot(const smt::TermVec & one_hot_vec, smt::SmtSolver & solver)
{
  smt::TermVec ret;
  auto ll = one_hot_vec.size();
  for (int i = 0; i < ll; i++) {
    for (int j = i + 1; j < ll; j++) {
      ret.push_back(solver->make_term(
          smt::Not,
          solver->make_term(smt::And,
                            { one_hot_vec.at(i), one_hot_vec.at(j) })));
    }
  }

  return ret;
}


smt::UnorderedTermMap get_model(const smt::Term & expr, smt::SmtSolver & solver)
{
  // cout << "get_model" << endl;
  smt::UnorderedTermMap ret_model;
  auto free_var_set = get_free_variables(expr);
  for (const auto & t : free_var_set) {
    ret_model.emplace(t, solver->get_value(t));
  }
  return ret_model;
}

smt::UnorderedTermMap get_invalid_model(const smt::Term & expr, smt::SmtSolver & solver)
{
  // cout << "get_invalid_model" << endl;
  auto expr_not = solver->make_term(smt::Not, expr);
  return get_model(expr_not, solver);
}

smt::Result is_sat_res(const smt::TermVec & expr_vec, smt::SmtSolver & solver)
{
  solver->push();
  for (const auto & a : expr_vec)
    solver->assert_formula(a);
  auto r = solver->check_sat();
  solver->pop();
  return r;
}

bool is_sat_bool(const smt::TermVec & expr_vec, smt::SmtSolver & solver)
{
  return is_sat_res(expr_vec, solver).is_sat();
}

bool is_valid_bool(const smt::Term & expr, smt::SmtSolver & solver)
{
  auto expr_not = solver->make_term(smt::Not, expr);
  return (! is_sat_bool(smt::TermVec{ expr_not }, solver));
}

std::vector<std::string> sort_model(const smt::UnorderedTermMap & cex)
{
  std::vector<std::string> cex_vec;
  for (const auto & sv : cex) {
    auto var = sv.first;
    auto value = sv.second;
    std::string cex_expr = var->to_string() + " := " + value->to_string();
    cex_vec.push_back(cex_expr);
  }
  std::sort(cex_vec.begin(), cex_vec.end());
  for (const auto & cex_str : cex_vec) {
    cout << cex_str << endl;
  }
  return cex_vec;
}

}  // namespace wasim
