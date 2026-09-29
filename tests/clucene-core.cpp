// Index two documents in memory and search them, through the installed
// headers in the compiler's default C++ mode.
#include <CLucene.h>
#include <cstdio>

using namespace lucene::analysis::standard;
using namespace lucene::document;
using namespace lucene::index;
using namespace lucene::queryParser;
using namespace lucene::search;
using namespace lucene::store;

int main() {
  RAMDirectory dir;
  StandardAnalyzer analyzer;
  {
    IndexWriter writer(&dir, &analyzer, true);
    const wchar_t *texts[] = {L"memory safe search engine", L"garbage in"};
    for (const wchar_t *text : texts) {
      Document doc;
      doc.add(*_CLNEW Field(L"body", text,
                            Field::STORE_YES | Field::INDEX_TOKENIZED));
      writer.addDocument(&doc);
    }
    writer.close();
  }
  IndexSearcher searcher(&dir);
  Query *query = QueryParser::parse(L"search", L"body", &analyzer);
  Hits *hits = searcher.search(query);
  size_t n = hits->length();
  const wchar_t *body = n ? hits->doc(0).get(L"body") : L"";
  std::printf("%zu %ls\n", n, body);
  bool ok = n == 1 && wcscmp(body, L"memory safe search engine") == 0;
  _CLDELETE(hits);
  _CLDELETE(query);
  searcher.close();
  return ok ? 0 : 1;
}
