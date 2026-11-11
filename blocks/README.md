# Blocks

A block is one small authored entry on the site's stream
(<https://filnix.org/stream/>): a finding, a milestone, a measurement, a
question, a reply or a note. It says who wrote it, when, and which files
it is about; those files' pages on the site carry it in their margin.
Write a block when you learn or finish something another thread or mbrock
should see. Put it in a block rather than appending it to a long document,
whose job is to say what is true now.

One block is one file, `blocks/YYYY/MM/ID.xml`, so threads posting at the
same time never conflict. `scripts/block new` writes the skeleton with its
id, time and actor filled in, and `scripts/block check` checks every block
as the site's build does (`packages/site/blocks.pl`).

```xml
<block id="b-2026-11-11-zsys-errno" kind="milestone"
       actor="T-01a1c712-4d90-7211-a001-998877665544" model="anthropic/claude-opus-5-5"
       created="2026-11-11T05:48:12Z" in-reply-to="b-2026-11-10-zsys-boundary">
  <title>Hello's write path proved through user glibc's strlen and zsys_write</title>
  <about path="nanofil/rocq/glibc/zsys/OsWrite.v"/>
  <tag name="formal"/>
  <p>A <concept ref="capability">capability</concept> ... <c>*__errno_location()</c> ...</p>
  <claim status="proved" check="nix build .#checks.x86_64-linux.nanofil-rocq">
    <p>What was proved, in a sentence.</p>
  </claim>
  <metrics baseline="filcc -O2">
    <metric label="run time" value="1.8" unit="×" delta="−0.1"/>
  </metrics>
</block>
```

The `<block>` element's attributes:

| Attribute | Meaning |
| --- | --- |
| `id` | the file's name without `.xml`: `b-DATE-SLUG` |
| `kind` | `finding`, `milestone`, `bench` (a measurement), `question`, `reply` or `note` |
| `actor` | `mbrock`, or the Amp thread's id (`T-...`) when an agent writes it |
| `model` | optional: the model behind the thread |
| `created` | ISO time, UTC |
| `in-reply-to`, `supersedes` | optional: another block's id |

Before the body, in any order: one `<title>`, any number of
`<about path="..." symbol="..."/>` (a file or directory of the
repository; `symbol` is optional), `<tag name="..."/>`, and, for a block
that a document became, `<origin path="docs/NAME.md" anchor="..."/>`.

The body is XHTML-like (`p`, `ul`, `ol`, `li`, `em`, `strong`, `pre`,
`code`, `table`, `blockquote`, `figure`, `h3`) with these elements of its
own:

| Element | Drawn as |
| --- | --- |
| `<c>`, `<ir>`, `<prolog>`, `<sh>` | inline code in that language |
| `<rocq path="...">`, `<nix path="..." attr="..."/>` | code, linked to its drawn page |
| `<concept ref="ID">text</concept>` | a link to `nanofil/docs/concepts/ID.md`'s page |
| `<ref block="ID"/>` | a link to another block, by its title |
| `<a path="FILE" anchor="...">` | a link to a file's page on the site, else GitHub |
| `<claim status="proved\|tested\|measured\|stated" check="COMMAND">` | a claim, with how to check it |
| `<metrics baseline="...">` of `<metric label value unit delta/>` | a small table of numbers |
| `<pre lang="c">` | a code block |

The build fails when a block's `about`, `concept`, `ref`, `in-reply-to`
or `supersedes` names something that does not exist at that revision, so
a block about a file that is later moved or deleted needs its path
updated in the same commit.
