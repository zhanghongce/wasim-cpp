#include "utils/container_shortcut.h"

namespace wasim
{
    
std::string Join(const std::vector<std::string> & vec, const std::string & delim) {
  std::string ret;
  for(const auto &s : vec) {
    if(!ret.empty())
      ret += delim;
    ret += s;
  }
  return ret;
}

} // namespace wasim

