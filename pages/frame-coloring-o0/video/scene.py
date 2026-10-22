"""A one-minute explainer for the -O0 frame slot coloring fix.

Render with ./render.sh, which writes ../explainer.mp4 and ../poster.png.

Captions are a few words each: a viewer can't stop to read, so the pictures
and their order carry the argument, and the page has the details. All text
goes through XeLaTeX in Public Sans, the wiki's font, for proper kerning.
"""

import os

from manim import *

PAPER = "#ffffff"
INK = "#111111"
MUTED = "#667078"
ACC = "#9a3248"  # the wiki's accent: conflicts, the old code
AMB = "#d98a1c"  # locals
BLU = "#2f6fb3"  # pointers, walking up
GRN = "#3d7a3d"  # placement, the new code

config.background_color = PAPER
config.pixel_width = 1080
config.pixel_height = 1080
config.frame_width = 8
config.frame_height = 8

TPL = TexTemplate(
    tex_compiler="xelatex",
    output_format=".xdv",
    documentclass=r"\documentclass[preview]{standalone}",
)
TPL.add_to_preamble(
    r"\usepackage{fontspec}"
    "\n"
    r"\setmainfont{PublicSans}[Path=" + os.environ["PUBLIC_SANS"] + r"/, Extension=.otf,"
    r" UprightFont=*-Regular, BoldFont=*-Bold]"
    "\n"
    r"\setmonofont{DejaVu Sans Mono}[Scale=MatchLowercase]"
)


def T(s, size=30, color=INK, bold=False):
    return Tex(r"\textbf{" + s + "}" if bold else s, tex_template=TPL, font_size=size, color=color)


def M(s, size=28, color=INK):
    return Tex(r"\texttt{" + s.replace("%", r"\%") + "}", tex_template=TPL, font_size=size, color=color)


def tok(name, color, r=0.24):
    c = Circle(r, fill_color=color, fill_opacity=1, stroke_width=0)
    return VGroup(c, T(name, int(r * 78), PAPER, bold=True).move_to(c))


def slot_row(n, y):
    sq = VGroup(
        *[RoundedRectangle(corner_radius=0.06, width=0.6, height=0.6, color=MUTED, stroke_width=2) for _ in range(n)]
    )
    sq.arrange(RIGHT, buff=0.08).move_to([0, y, 0])
    idx = VGroup(*[T(str(i), 18, MUTED).next_to(s, DOWN, 0.08) for i, s in enumerate(sq)])
    lab = T("frame slots", 20, MUTED).next_to(sq, UP, 0.12).align_to(sq, LEFT)
    return sq, idx, lab


def counter(tracker, size, color, place):
    return always_redraw(lambda: place(T(f"{tracker.get_value():,.0f}", size, color, bold=True)))


class Explainer(Scene):
    cap = None

    def caption(self, s, color=INK, size=46):
        c = VGroup(*[T(line, size, color, bold=True) for line in s.split("\n")]).arrange(DOWN, buff=0.15)
        if c.width > 7.3:
            c.scale_to_fit_width(7.3)
        c.to_edge(UP, buff=0.55)
        if self.cap is None:
            self.play(FadeIn(c, shift=DOWN * 0.2), run_time=0.5)
        else:
            self.play(FadeOut(self.cap, shift=UP * 0.2), FadeIn(c, shift=UP * 0.2), run_time=0.5)
        self.cap = c

    def clear_all(self):
        self.play(*[FadeOut(m) for m in self.mobjects], run_time=0.5)
        self.cap = None

    def construct(self):
        # 1. The hook.
        big = T("48 seconds", 110, ACC, bold=True)
        sub = T("to compile one function at \\texttt{-O0}", 36, MUTED).next_to(big, DOWN, 0.4)
        self.play(FadeIn(big, scale=0.9), run_time=0.8)
        self.play(FadeIn(sub))
        self.wait(1.2)
        self.play(FadeOut(big), FadeOut(sub), run_time=0.5)

        # 2. Pointers share slots unless they overlap.
        self.caption("Pointers live in slots")
        sq, idx, lab = slot_row(8, -2.6)
        self.play(LaggedStart(*[Create(s) for s in sq], lag_ratio=0.05), FadeIn(idx), FadeIn(lab), run_time=0.8)
        axis = Arrow([-3.3, -0.9, 0], [3.3, -0.9, 0], color=MUTED, stroke_width=2, buff=0,
                     max_tip_length_to_length_ratio=0.03)
        tl = T("time", 20, MUTED).next_to(axis, DOWN, 0.08).align_to(axis, RIGHT)
        spans = {"p": (-2.6, -0.6, 0.9), "q": (0.4, 3.0, 0.9), "r": (-1.6, 1.4, 0.0)}
        bars, toks = {}, {}
        for n, (x0, x1, y) in spans.items():
            bars[n] = Line([x0, y, 0], [x1, y, 0], color=BLU, stroke_width=12)
            toks[n] = tok(n, BLU).next_to(bars[n], LEFT, 0.1)
        self.play(Create(axis), FadeIn(tl), *[Create(b) for b in bars.values()],
                  *[FadeIn(t) for t in toks.values()], run_time=0.8)
        self.caption("Apart: share")
        self.play(toks["p"].animate.scale(0.75).move_to(sq[0].get_center() + LEFT * 0.14),
                  toks["q"].animate.scale(0.75).move_to(sq[0].get_center() + RIGHT * 0.14))
        self.caption("Overlap: conflict", ACC)
        hl = VGroup(
            Rectangle(width=1.0, height=1.3, color=ACC, stroke_width=3).move_to([-1.1, 0.45, 0]),
            Rectangle(width=1.0, height=1.3, color=ACC, stroke_width=3).move_to([0.9, 0.45, 0]),
        )
        self.play(Create(hl), run_time=0.5)
        self.play(toks["r"].animate.scale(0.75).move_to(sq[1]))
        self.wait(0.8)
        self.clear_all()

        # 3. At -O0 every local is always live, so it conflicts with everything.
        self.caption("\\texttt{-O0}: locals live forever")
        locs = VGroup(*[tok(f"a{i}", AMB) for i in range(6)]).arrange(DOWN, buff=0.2).move_to([-2.5, -0.5, 0])
        ptrs = VGroup(*[tok(f"p{i}", BLU, 0.2) for i in range(12)]).arrange_in_grid(4, 3, buff=0.5)
        ptrs.move_to([1.7, -0.5, 0])
        self.play(LaggedStart(*[FadeIn(m) for m in [*locs, *ptrs]], lag_ratio=0.03), run_time=0.8)
        edges = VGroup()
        for i in range(6):
            for j in range(i + 1, 6):
                edges.add(ArcBetweenPoints(locs[i].get_left(), locs[j].get_left(), angle=PI * 0.6,
                                           color=ACC, stroke_width=1.5, stroke_opacity=0.7))
        for a in locs:
            for p in ptrs:
                edges.add(Line(a.get_right(), p.get_left(), color=ACC, stroke_width=1.2, stroke_opacity=0.4))
        n_edges = ValueTracker(0)
        cnt = counter(n_edges, 44, ACC, lambda m: m.move_to([0, -3.2, 0]))
        cnt_lab = T("conflicts", 22, MUTED).move_to([0, -3.65, 0])
        self.add(cnt, cnt_lab)
        self.play(LaggedStart(*[Create(e) for e in edges], lag_ratio=0.02),
                  n_edges.animate.set_value(len(edges)), run_time=2.5)
        self.bring_to_front(locs, ptrs)
        self.caption("Real function:\n4 million conflicts", ACC)
        self.wait(1.4)

        # 4. The old search rescans the whole conflict list for every slot it tries.
        self.caption("Old: try a slot, rescan all")
        sq, idx, lab = slot_row(8, -2.6)
        p = ptrs[0]
        self.remove(cnt)
        self.play(FadeOut(edges), FadeOut(cnt_lab), FadeOut(ptrs[1:]), Create(sq), FadeIn(idx), FadeIn(lab), run_time=0.6)
        self.play(*[locs[i].animate.scale(0.9).move_to(sq[i]) for i in range(6)],
                  p.animate.scale(1.3).move_to([-2.0, 0.6, 0]), run_time=0.6)
        order = ["a3", "p4", "a0", "a5", "p7", "a1", "a4", "p2", "a2"]
        lst = VGroup(*[
            VGroup(RoundedRectangle(corner_radius=0.05, width=0.9, height=0.34, color=MUTED, stroke_width=1,
                                    fill_color=AMB if n[0] == "a" else BLU, fill_opacity=0.25),
                   T(n, 18))
            for n in order
        ]).arrange(DOWN, buff=0.06).move_to([2.6, 0.2, 0])
        for g in lst:
            g[1].move_to(g[0])
        n_checks = ValueTracker(0)
        chk = counter(n_checks, 52, ACC, lambda m: m.move_to([-2.0, -1.1, 0]))
        chk_lab = T("checks", 22, MUTED).move_to([-2.0, -1.6, 0])
        self.play(FadeIn(lst), FadeIn(chk_lab), run_time=0.4)
        self.add(chk)
        scan = SurroundingRectangle(lst[0], color=INK, buff=0.03, stroke_width=3)
        arrow = Triangle(color=ACC, fill_opacity=1).scale(0.13).rotate(PI).next_to(sq[0], UP, 0.42)
        self.play(FadeIn(scan), FadeIn(arrow), run_time=0.3)
        checks = 0
        for s in range(6):
            self.play(arrow.animate.next_to(sq[s], UP, 0.42), run_time=0.15)
            for k, n in enumerate(order):
                checks += 1
                self.play(scan.animate.move_to(lst[k]), n_checks.animate.set_value(checks), run_time=0.05)
                if n == f"a{s}":
                    self.play(Indicate(lst[k], color=ACC, scale_factor=1.15), run_time=0.2)
                    break
        self.play(arrow.animate.next_to(sq[6], UP, 0.42).set_color(GRN), p.animate.scale(0.7).move_to(sq[6]),
                  run_time=0.5)
        self.caption("Real function:\n1.5 billion checks", ACC)
        self.wait(1.4)
        self.remove(chk)
        self.clear_all()

        # 5. The idea: the live locals are always the first k, and so are the placed ones.
        self.caption("Locals sit at the top")
        lines = [f"%a{i} = alloca" for i in range(6)] + ["%p = load %a1", "...", "%q = load %a4"]
        code = VGroup(*[M(line, 28, AMB if i < 6 else INK) for i, line in enumerate(lines)])
        code.arrange(DOWN, buff=0.17, aligned_edge=LEFT).move_to([-1.6, -0.3, 0])
        hls = VGroup(*[SurroundingRectangle(code[i], buff=0.05, stroke_width=0, fill_color=AMB, fill_opacity=0.28)
                       for i in range(6)])
        self.play(FadeIn(code), run_time=0.5)
        ys = [code[i].get_top()[1] + 0.09 for i in range(len(lines))] + [code[-1].get_bottom()[1] - 0.09]
        cur = Line([-3.3, ys[-1], 0], [0.6, ys[-1], 0], color=BLU, stroke_width=4)
        side = T("live", 30, BLU, bold=True).move_to([2.4, 0.5, 0])
        kt = T("first 6", 46, BLU, bold=True).next_to(side, DOWN, 0.2)
        self.play(Create(cur), FadeIn(side), FadeIn(hls), FadeIn(kt), run_time=0.5)
        for i in range(len(lines) - 1, -1, -1):
            k = min(i, 6)
            self.play(cur.animate.move_to([cur.get_center()[0], ys[i], 0]),
                      *[hls[j].animate.set_fill(opacity=0.28 if j < k else 0) for j in range(6)],
                      Transform(kt, T(f"first {k}", 46, BLU, bold=True).move_to(kt)), run_time=0.3)
        self.caption("Placement: same order", GRN)
        sq, idx, lab = slot_row(8, -3.1)
        self.play(FadeIn(sq), FadeIn(idx), FadeIn(lab), cur.animate.set_color(GRN),
                  Transform(side, T("placed", 30, GRN, bold=True).move_to(side)),
                  Transform(kt, T("first 0", 46, GRN, bold=True).move_to(kt)), FadeOut(hls), run_time=0.5)
        for i in range(6):
            t = tok(f"a{i}", AMB, 0.22).move_to(code[i].get_left() + LEFT * 0.35)
            self.add(t)
            self.play(cur.animate.move_to([cur.get_center()[0], ys[i + 1], 0]),
                      Transform(kt, T(f"first {i + 1}", 46, GRN, bold=True).move_to(kt)),
                      t.animate.move_to(sq[i]), sq[i].animate.set_fill(AMB, 0.3), run_time=0.35)
        brace = Brace(VGroup(sq[0], sq[5]), DOWN, color=AMB, buff=0.35)
        bt = T("taken", 22, AMB, bold=True).next_to(brace, DOWN, 0.05)
        self.play(GrowFromCenter(brace), FadeIn(bt), run_time=0.4)
        self.caption("Skip the taken slots.\nStore nothing.", GRN)
        pt = tok("p", BLU, 0.22).move_to(code[6].get_left() + LEFT * 0.35)
        self.play(cur.animate.move_to([cur.get_center()[0], ys[7], 0]), FadeIn(pt), run_time=0.4)
        self.play(pt.animate.move_to(sq[6]), Indicate(sq[6], color=GRN), run_time=0.6)
        self.wait(1.4)
        self.clear_all()

        # 6. The result.
        self.caption("Same function, \\texttt{-O0}")
        t = ValueTracker(0)
        width, x0 = 4.4, -2.4

        def bar(cap_s, y, color):
            return always_redraw(lambda: Rectangle(
                width=max(0.01, width * min(t.get_value(), cap_s) / 48), height=0.55, stroke_width=0,
                fill_color=color, fill_opacity=1).move_to([x0, y, 0], aligned_edge=LEFT))

        rows = VGroup(T("before", 32, bold=True).move_to([-3.1, 0.9, 0]),
                      T("after", 32, bold=True).move_to([-3.1, -0.1, 0]))
        before = always_redraw(lambda: T(f"{min(t.get_value(), 48):.0f} s", 32, ACC, bold=True).move_to(
            [x0 + width * min(t.get_value(), 48) / 48 + 0.5, 0.9, 0], aligned_edge=LEFT))
        after = T("0.66 s", 32, GRN, bold=True).move_to([x0 + 0.2, -0.1, 0], aligned_edge=LEFT)
        self.add(rows, bar(48, 0.9, ACC), bar(0.66, -0.1, GRN), before)
        self.play(t.animate.set_value(0.66), run_time=0.1, rate_func=linear)
        self.add(after)
        self.play(t.animate.set_value(48), run_time=4.0, rate_func=linear)
        same = T("Same slots in all 44,006 functions", 34, GRN, bold=True).move_to([0, -1.7, 0])
        self.play(FadeIn(same, shift=UP * 0.2))
        url = T("mbrock.github.io/filnix/frame-coloring-o0", 26, ACC).move_to([0, -3.2, 0])
        self.play(FadeIn(url))
        self.wait(2.5)
