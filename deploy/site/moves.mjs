// Pages the site has moved, as migrations: each move takes a canonical
// path that a restructuring removed and gives where that page lives now,
// or nothing. The Worker asks only after a path is not found, so a page
// that exists again is served, never redirected. Moves apply in order,
// each to what the ones before it gave, so a link from before several
// restructurings follows all of them. Add a new move at the end, with
// the commit or document that made it.

// The Rocq model's theories, one directory per layer
// (nanofil/rocq/theories/LAYER/NAME.v, November 2026): their pages went
// from rocq-theories-NAME.html to rocq-theories-LAYER-NAME.html.
const rocqLayers = {
  core: "Cfg Extract Ieee Maps Memory Ops Run Runtime Semantics Syntax Term Transport ValidFast Validate Values",
  soundness: "Ahead Chain Coverage Dominance Doomed Evidence Guard Identity Interval Invariant Machine Persistence Renew Single Sites Soundness Steps Walk",
  external: "ExternalCalls ExternalMachine Libio Shutdown Startup Stdio",
  logic: "ContractFrame Heap Language Logic MemLogic Panics Pieces StepRules StringLogic Symbolic",
  programs: "Buffer BufferCode BufferLogic Composition CountCode CountLogic Cycle CycleCode Hi HiArtifact HiCode HiLogic Program ScanCode ScanLogic Selected SlotCode SlotLogic Sum SumCode",
  hello_contracts: "CallbackLogic Diagnostics Ending ExitMemory Formatting Getopt GetoptLogic HelloClose HelloCode HelloConv HelloConvDefs HelloDiagnosticChecks HelloJoin HelloLeaf HelloLocale HelloMain HelloModule HelloName HelloProgName HelloReach HelloStdio HelloVersion HelloWorld LentLogic Libc LibcDiagnosticLogic LibcErrnoLogic LibcExit LibcStreamAdapter LibcStreamLogic LibcStreamTokens LibcStreams Linked Locale LocaleLogic Streams",
};
const rocqLayer = new Map(Object.entries(rocqLayers).flatMap(
  ([layer, names]) => names.split(" ").map(name => [name, layer])));

const moves = [
  path => {
    const m = path.match(/^\/nanofil\/rocq\/rocq-theories-(\w+)\.html$/);
    const layer = m && rocqLayer.get(m[1]);
    return layer && `/nanofil/rocq/rocq-theories-${layer}-${m[1]}.html`;
  },
  // The hand-rolled separation-logic spike (rocq/spikes/Sep.v and
  // SepListSum.v), removed in November 2026: Sep.v to the program logic
  // that replaced it, and its list-sum proof to the same proof there.
  path => ({
    "/nanofil/rocq/rocq-spikes-Sep.html": "/nanofil/rocq/rocq-theories-logic-Logic.html",
    "/nanofil/rocq/rocq-spikes-SepListSum.html": "/nanofil/rocq/rocq-spikes-ListSumLogic.html",
  })[path],
];

// moved(path): where the page at a removed canonical path is now, or
// null when no move names it.
export function moved(path) {
  let now = path;
  for (const move of moves) now = move(now) || now;
  return now === path ? null : now;
}

// Pages the site still publishes but a newer page replaces, so readers go
// to the replacement. The Worker redirects these before serving them.
export const superseded = new Map([
  // ZsysWrite.v's zsys_write contract, restated over os_world by
  // zsys/OsWrite.v (16a77c83). SayLogic.v still imports ZsysWrite.v.
  ["/nanofil/rocq/rocq-glibc-ZsysWrite.html", "/nanofil/rocq/rocq-glibc-zsys-OsWrite.html"],
]);
