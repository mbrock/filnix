#include <iostream>
#include <string>
#include <string_view>
#include <optional>
#include <charconv>
#include <cstdlib>

using namespace std;

auto url_decode(string_view encoded) -> string {
  string result;
  for (size_t i = 0; i < encoded.size(); ++i) {
    if (encoded[i] == '+') {
      result += ' ';
    } else if (encoded[i] == '%' && i + 2 < encoded.size()) {
      int value;
      auto [ptr, ec] = from_chars(encoded.data() + i + 1,
                                  encoded.data() + i + 3, value, 16);
      if (ec == errc{}) {
        result += static_cast<char>(value);
        i += 2;
      } else {
        result += encoded[i];
      }
    } else {
      result += encoded[i];
    }
  }
  return result;
}

auto extract_param(string_view query, string_view param) -> optional<string> {
  string pattern = string(param) + "=";

  for (size_t pos = 0; pos < query.size();) {
    pos = query.find(pattern, pos);
    if (pos == string_view::npos) break;

    if (pos == 0 || query[pos - 1] == '&') {
      pos += pattern.size();
      auto end = query.find('&', pos);
      auto value = query.substr(pos, end - pos);
      return url_decode(value);
    }
    ++pos;
  }
  return nullopt;
}

int main(int argc, char* argv[]) {
  if (argc != 2) {
    cerr << "Usage: " << argv[0] << " PARAM_NAME\n";
    return 1;
  }

  if (auto query = getenv("QUERY_STRING")) {
    if (auto value = extract_param(query, argv[1])) {
      cout << *value;
    }
  }
  return 0;
}
