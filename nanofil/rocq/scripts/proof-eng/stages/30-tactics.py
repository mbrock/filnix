#!/usr/bin/env python3
"""Consolidate instruction tactics after flattening, without editing statements."""
import re
import sys
import hashlib
from pathlib import Path


def masked(text, hide_strings=True):
    """Hide nested comments and strings, preserving character positions and newlines."""
    out = list(text)
    i = depth = 0
    string = False
    while i < len(text):
        pair = text[i:i + 2]
        if not string and pair == "(*":
            depth += 1
            out[i:i + 2] = "  "
            i += 2
            continue
        if depth and pair == "*)":
            depth -= 1
            out[i:i + 2] = "  "
            i += 2
            continue
        if not depth and text[i] == '"':
            if string and pair == '""':
                if hide_strings:
                    out[i:i + 2] = "  "
                i += 2
                continue
            string = not string
            if hide_strings:
                out[i] = " "
        elif depth or (string and hide_strings):
            if text[i] != "\n":
                out[i] = " "
        i += 1
    if depth or string:
        raise ValueError("unterminated comment or string")
    return "".join(out)


def tactics(text):
    code = masked(text)
    for m in re.finditer(r"\b(?:(?:Local|Global)\s+)?Ltac\s+([\w']+)(?![\w'])", code):
        end = re.search(r"\.(?=\s|$)", code[m.end():])
        if not end:
            raise ValueError(f"unterminated Ltac {m[1]}")
        yield m[1], m.start(), m.end() + end.end()


RENAMES = dict(st="step", fs="step", chk="check", fchk="check",
               br="branch", fbr="branch", brv="branch_as", fbrv="branch_as",
               brc="branch_cases", fldp="load", fstp="store", fldi="load_s32",
               fsti="store_int", fldn="load_null", fstl="store_long", enter="step",
               ldi="load_s32_group", ldb="load_byte_group", sti="store_int_group",
               ldp="load_group", stp="store_group", chkq="check_shared",
               ldbp="load_byte_persistent", chkp="check_persistent",
               load_int="load_s32_group", vx="vx", inst="inst", ins="inst",
               rule1="rule1", rule2="rule2", rule3="rule3",
               step="concrete_step", vm_eq="vm_eq", replace_env="replace_env", norm_env="norm_env",
               st_global="step_global", en="step", sl="step_symbolic", sf="step", sv="step_symbolic",
               sg="(step; step)", sb="branch_symbolic", sn="step_named", slk="step_lookup")
RENAMES.update({"sl'": "step_symbolic", "sf'": "step", "sb'": "branch_symbolic"})
RENAMES.update(pst="step_symbolic", fbrm="branch_rewrite", fbrw="branch_rewrite",
               load_pointer="load_shared",
               load_self="load_self_using (wp_raw_load_pointer_self w0 registry ge)")
RENAMES.update({n: RENAMES["load_self"] for n in
                ("printf_overflow_entry_load_self", "xsputn_entry_load_self")})

# These are the reviewed pure-step bodies, not filenames. A newly generated
# lane file using any of these bodies is converted without being listed here.
# Changed implementations fail closed rather than silently losing behavior.
PURE_ST = {"37e85d324383c22f", "401c42379d0c48ff", "46930f1a2983ed0a",
           "4b9828e8b945ef8c", "7638b14a7e9a99c9", "d62d82279811ba08"}
VALUES = {"23d52ea201bf5a00", "976363f141b35f17", "d816db67e02459c8"}
LIBRARY_BODIES = {
    "enter": "5e3e41a779e13a5e", "chk": "d98c10525e4a2e0e",
    "br": "472a25d3f7c3a10c", "brc": "ab41664f62a5bf2d",
    "brv": "87cc1eddbc524e7d", "fs": "00168a558da54c85",
    "fbr": "b92e4830f5b86fb7", "fbrv": "9af43936cf33544f",
    "fchk": "82d8731c296517d6", "fldi": "3724603cfe667316",
    "fsti": "de8c04e3db30d240", "fldp": "5d704e63d48f49b0",
    "fldn": "c05b24224e5b3ef7", "fstl": "55e9ff470e01a78e",
    "fstp": "1badcff7549eb0f2"}


def body(text):
    code = masked(text, hide_strings=False).split(":=", 1)[1]
    return re.sub(r'"(?:[^"]|"")*"|\s+',
                  lambda m: m[0] if m[0].startswith('"') else "", code)


def recognized(name, text, library):
    if name == "step":
        text = re.sub(r"\bside\b", "concrete_side", text)
    normalized = body(text)
    if name == "st_global":
        normalized = normalized.replace(";ins;", ";inst;")
    if name in RENAMES and normalized == library.get(RENAMES[name]):
        return True
    if name == "load_int":
        canonical = normalized.replace("|arith|", "|ar|").replace(
            "[reflexivity|reflexivity|reflexivity|applyload_sw_int;",
            "[reflexivity|vx|reflexivity|applyload_sw_int;")
        if canonical == library["load_s32_group"]:
            return True
    if name in {"load_self", "printf_overflow_entry_load_self", "xsputn_entry_load_self"} and normalized.replace(
            "wp_raw_load_pointer_selfw0registryge", "rule") == library["load_self_using"]:
        return True
    if name in {"fbrm", "fbrw"} and normalized.replace("rewriteH;", "rewriteE;") == (
            "eapplystep_wand;[eapplywp_branch;inst;vx|];rewriteE;"
            "lazymatchgoalwith|-context[edge_label(if?cthen_else_)]=>"
            "letc':=vm_ofcinchangecwithc'end;cbn[edge_label]."):
        return True
    if name == "br" and normalized.replace(";ins;", ";inst;") in {
            "eapplystep_wand;[eapplywp_branch;inst;vx|];decide_branch.",
            "eapplystep_wand;[eapplywp_branch;inst;reflexivity|];decide_branch."}:
        return True
    if name == "pst" and normalized == (
            "iApplywp_let;[reflexivity|reflexivity|reflexivity|intros?;reflexivity|iNext]."):
        return True
    lifted = normalized
    for rule in ("s_let", "s_letn", "s_flight", "s_enter", "s_goto", "s_branch"):
        lifted = lifted.replace("(" + rule + "registrywige)", rule)
    pure = {
        "eapplys_let;[reflexivity|reflexivity|reflexivity|intros?;reflexivity|].",
        "eapplys_let;[reflexivity|reflexivity|vx|intros?;reflexivity|].",
        "eapplys_let;[reflexivity|reflexivity|vxf|intros?;reflexivity|].",
        "eapplys_flight;[reflexivity|reflexivity|reflexivity|].",
        "eapplys_flight;[vx|reflexivity|vx|].",
        "eapplys_enter;[reflexivity|reflexivity|];cbn[b_instsb_jump].",
        "iApplywp_enter;[reflexivity|reflexivity|iNext];cbn[b_instsb_jump].",
    }
    if name in {"sl", "sl'", "sf", "sf'", "sv", "en"} and lifted in pure:
        return True
    if name == "sg" and lifted == "eapplys_goto;en.":
        return True
    if name in {"sb", "sb'"} and lifted in {
            "eapplys_branch;[reflexivity|].", "eapplys_branch;[vx|]."}:
        return True
    if name == "sn" and lifted == (
            'eapplys_letn;[reflexivity|reflexivity|reflexivity|intros?;reflexivity|];'
            'letx:=fresh"x"inletE:=fresh"E"inintrosxE.'):
        return True
    if name == "slk" and lifted == (
            'eapplys_let;[reflexivity|reflexivity|cbn[map2_optionvalue_x];'
            'repeat(rewrite(lookup_after_put_other_(TAtomn));[|reflexivity]);'
            'rewriteH;reflexivity|intros?;reflexivity|].'):
        return True
    digest = hashlib.sha256(normalized.encode()).hexdigest()[:16]
    if name == "st":
        if digest not in PURE_ST:
            raise ValueError("unrecognized st body: " + text)
        return True
    if name == "vx":
        if digest not in VALUES:
            raise ValueError("unrecognized vx body: " + text)
        return True
    return digest == LIBRARY_BODIES.get(name)


def replacement(name, text):
    normalized = body(text)
    if name == "load_int" and "|arith|" in normalized:
        return "load_s32_using ltac:(arith)"
    if name == "br" and normalized.endswith(";decide_branch."):
        return "(branch_symbolic; LeavesLogic.decide_branch)"
    return RENAMES[name]


SIDES = {"GlibcLogic": "concrete_side", "LibioLogic": "libio_side",
         "LibioCloseSteps": "close_side"}


def edit_imports(text, stream=None, remove=()):
    """Keep header adaptation in one place as flattening's runtime mode evolves."""
    for m in reversed(list(re.finditer(
            r"(?:\bFrom Glibc Require (?:Import |Export )?|\bImport )([\w.\s]+?)\.(?=\s|$)",
            masked(text)))):
        part = text[m.start():m.end()]
        for name in remove:
            part = re.sub(r"\b" + name + r"\b", "", part)
        text = text[:m.start()] + part + text[m.end():]
    if stream is None:
        return text
    first = re.search(r"^From\s", masked(text), re.M)
    if not first:
        raise ValueError("proof has no import header")
    k = first.start()
    modules = "GlibcTactics LibioTactics" if stream else "GlibcTactics"
    return text[:k] + f"From Glibc Require Import {modules}.\n" + text[k:]


def side_name(text, module, definitions):
    """Resolve the three distinct solvers in the original flat import order."""
    result = None
    for m in re.finditer(r"\bImport\s+([\w.\s]+?)\.(?=\s|$)", masked(text)):
        for name in m[1].split():
            if name in SIDES and "side" in definitions.get(name, ()):
                result = SIDES[name]
    if module in SIDES and "side" in definitions.get(module, ()):
        result = SIDES[module]
    return result


def rewrite_tactics(text, names):
    """Rewrite tactic positions, never theorem statements, comments or strings."""
    code = masked(text)
    spans = [(a, b) for _, a, b in tactics(text)]
    for m in re.finditer(r"\bProof\b[^.]*\.", code):
        end = re.search(r"\b(?:Qed|Defined|Admitted|Abort)\.", code[m.end():])
        if end:
            spans.append((m.end(), m.end() + end.end()))
    changes = []
    start = re.compile(
        r"(?:^|[.;|\[\]{}:+*-]|=>|:=|\b(?:try|repeat|progress|once|first|solve)|\bdo\s+\d+)\s*(?:\(\s*)*$")
    for a, b in spans:
        # Parentheses and brackets after a term-taking tactic are arguments,
        # not tactic sequences: iIntros (fs ...), destruct ... as [st | fs],
        # and cbn [st] must retain their identifiers. A nested ltac:(...) is
        # deliberately a tactic again, even inside a lemma argument.
        protected = set()
        stack = []
        for k in range(a, b):
            if code[k] in "([":
                prefix = code[a:k]
                quoted = re.search(r"\bltac:\s*$", prefix)
                stack.append(not quoted and ((stack and stack[-1]) or not start.search(prefix)))
            if stack and stack[-1]:
                protected.add(k)
            if code[k] in ")]" and stack:
                stack.pop()
        for m in re.finditer(r"\b[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*(?![\w'])", code[a:b]):
            prefix = code[a:a + m.start()]
            if m[0] in names and a + m.start() not in protected and start.search(prefix):
                changes.append((a + m.start(), a + m.end(), names[m[0]]))
    for a, b, value in sorted(set(changes), reverse=True):
        text = text[:a] + value + text[b:]
    return text


def main(root):
    sources = {p.stem: p.read_text() for p in root.rglob("*.v")}
    overlay = (Path(__file__).parent.parent / "overlay/GlibcTactics.v").read_text()
    library = {n: body(overlay[a:b]) for n, a, b in tactics(overlay)}
    stream_overlay = (Path(__file__).parent.parent / "overlay/libio/LibioTactics.v").read_text()
    stream_library = {n: body(stream_overlay[a:b]) for n, a, b in tactics(stream_overlay)}
    library.update(stream_library)
    definitions = {module: {n for n, a, _ in tactics(text)
                            if not text[a:].startswith("Local")}
                   for module, text in sources.items()}
    migrate = {module: {n: replacement(n, text[a:b]) for n, a, b in tactics(text)
                        if recognized(n, text[a:b], library)}
               for module, text in sources.items()}
    qualified = {}
    for module, replacements in migrate.items():
        for name, value in replacements.items():
            if name in definitions[module]:
                head = value.split()[0]
                owner = "LibioTactics" if head in stream_library else "GlibcTactics"
                target = owner + "." + value if head in library else value
                for prefix in (module, "Glibc." + module):
                    qualified[prefix + "." + name] = target
    qualified_sides = {prefix + ".side": module + "." + solver
                       for module, solver in SIDES.items()
                       if "side" in definitions.get(module, ())
                       for prefix in (module, "Glibc." + module)}
    # Stream rules stay above the generic library. Their old import of
    # SysWrappers was only for aliases and would cycle through LibioTactics.
    close = root / "libio/LibioCloseSteps.v"
    text = close.read_text()
    text = edit_imports(text, remove=("SysWrappers", "SysCode"))
    close.write_text(text)
    sources[close.stem] = text
    support = set()
    pending = ["Fix", "FileInv", "LibioLogic", "LibioCloseSteps"]
    while pending:
        module = pending.pop()
        if module in support:
            continue
        support.add(module)
        for m in re.finditer(r"From Glibc Require (?:Import |Export )?([\w\s]+)\.",
                             masked(sources.get(module, ""))):
            pending.extend(m[1].split())

    removed = 0
    for path in sorted(root.rglob("*.v")):
        text = path.read_text()
        owners = {}
        for m in re.finditer(r"\bImport\s+([\w.\s]+?)\.(?=\s|$)", masked(text)):
            for module in m[1].split():
                for name in definitions.get(module, ()):
                    owners[name] = module
        names = {name: migrate[owner][name] for name, owner in owners.items()
                 if name in migrate.get(owner, {})}
        # Explicit owners survive import shadowing and must be rewritten as
        # whole identifiers, including when their old definition is removed.
        names.update(qualified)
        text = rewrite_tactics(text, qualified_sides)
        solver = side_name(text, path.stem, definitions)
        if solver:
            # A future main may already name the solver and retain an alias.
            # Remove only a literal alias; never overwrite another solver body.
            for name, a, b in reversed(list(tactics(text))):
                if name == "side" and body(text[a:b]) == solver + ".":
                    text = text[:a] + text[b:]
                    removed += 1
            text = rewrite_tactics(text, {"side": solver})
            if path.stem in SIDES:
                for name, a, b in reversed(list(tactics(text))):
                    if name == "side":
                        if solver in {n for n, _, _ in tactics(text)}:
                            raise ValueError(f"{path}: both side and {solver} have bodies")
                        definition = text[a:b].replace("Ltac side", "Ltac " + solver, 1)
                        text = text[:a] + definition + text[b:]
        local = list(tactics(text))
        for name, a, b in reversed(local):
            if name in migrate[path.stem]:
                text = text[:a] + text[b:]
                names[name] = migrate[path.stem][name]
                removed += 1
            elif name in names:
                del names[name]
        text = rewrite_tactics(text, names)
        remaining = set(re.findall(
            r"\b[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)+(?![\w'])", masked(text))) & qualified.keys()
        if remaining:
            raise ValueError(f"{path}: qualified uses of removed tactics remain: {sorted(remaining)}")
        # Move only identical generic statements and proofs, modulo comments
        # and whitespace. Their names remain available through the shared import.
        for m in reversed(list(re.finditer(
                r"\bLemma (step_wand|step_res[123]|lookup_put_miss)\b[\s\S]*?\bQed\.",
                masked(text)))):
            original = text[m.start():m.end()]
            target = re.search(r"\bLemma " + m[1] + r"\b[\s\S]*?\bQed\.", overlay)
            normalize = lambda s: re.sub(r"\s+", "", masked(s, hide_strings=False))
            if target and normalize(original) == normalize(target[0]):
                text = text[:m.start()] + text[m.end():]
        # Replace long field lists by a database populated at their definitions.
        for m in reversed(list(re.finditer(
                r"unfold (off_cleanup,\s*off_cleanup_jmp,[^;]+);", masked(text)))):
            text = text[:m.start()] + "autounfold with offs;" + text[m.end():]
        if path.name == "FileInv.v":
            for m in reversed(list(re.finditer(
                    r"Definition ((?:off_|vt_|slot_)\w+)\b[\s\S]*?\.(?=\s|$)", masked(text)))):
                text = text[:m.end()] + f"\n#[export] Hint Unfold {m[1]} : offs." + text[m.end():]
        if path.stem != "Fix" and (re.search(r"\b(?:Proof|Ltac)\b", masked(text)) or path.stem == "FileInv"):
            text = edit_imports(text, stream=path.stem not in support and
                              any(value.split()[0] in stream_library or
                                  value.startswith("LibioTactics.") and value in text
                                  for value in names.values()))
        if re.search(r"\bside\b", masked(text)):
            raise ValueError(f"{path}: unresolved legacy side reference; retain its alias until reviewed")
        path.write_text(text)
    project = root / "_RocqProject"
    if project.exists():
        text = project.read_text()
        for path in ("GlibcTactics.v", "libio/LibioTactics.v"):
            if path not in text.splitlines():
                text += path + "\n"
        project.write_text(text)
    print(f"tactics: removed {removed} instruction tactic definitions")


if __name__ == "__main__":
    main(Path(sys.argv[1]))
