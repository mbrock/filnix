# Rocq prose

- Write comments in the style of the GNU Emacs manual for a strong systems programmer who does not know Iris. Explain the concrete C or Fil-C problem before naming its Rocq definition.
- Use complete subject–verb–object sentences with plain verbs, usually 12–25 words. Replace dictionary captions and lemma inventories with explanations of what a proof needs and why.
- Begin every `##` section with two or three sentences that orient the reader before the definitions.
- Link a concept's first mention with `[[concept]]`, using the names in `../docs/concepts/`. Link Rocq names with `[name]`. Leave single-letter variables in ordinary prose rather than backticks.
- Use ordinary paragraphs instead of italics or Markdown pipe tables, which do not render as intended on these pages. Preserve fenced C examples.
- Use the explanation of borrowed caller memory in `theories/logic/ContractFrame.v` as an example of introducing proof concepts through a concrete problem.
- For prose-only edits, preserve every non-comment byte, including whitespace. From the repository root, check the changed modules with `scripts/prose-check -v --all-comments --max-passages 64 FILE...`, increasing the limit to cover any remaining passages; require zero flags. Build the modules, compile their parser reprints with `nanofil/web/rocq/tests/parse.sh`, check documentation references with `nanofil/web/dterm.pl --check`, and inspect the rendered pages.
