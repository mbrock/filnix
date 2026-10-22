"""A 45-second video for Fil-BIND: BIND 9 compiled with Fil-C.

Render with ./render.sh, which writes ../fil-bind.mp4 and ../poster.png. It is
16:9 at 1920x1080 so that it plays full width on the page and on Twitter.

As in the frame-coloring explainer, captions are a few words each and the
pictures carry the argument; the page has the details and the sources.
"""

import os

from manim import *

PAPER = "#ffffff"
INK = "#111111"
MUTED = "#667078"
FAINT = "#c9cdd1"
ACC = "#9a3248"  # corruption, the attacker's win
AMB = "#d98a1c"  # the neighbouring secret
BLU = "#2f6fb3"  # the pointer
GRN = "#3d7a3d"  # Fil-C

SLOWDOWN = os.environ.get("FILBIND_SLOWDOWN", "5–6")

config.background_color = PAPER
config.pixel_width = 1920
config.pixel_height = 1080
config.frame_height = 8
config.frame_width = 8 * 16 / 9

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
    return Tex(r"\texttt{" + s + "}", tex_template=TPL, font_size=size, color=color)


def cell(color=MUTED, fill=None):
    return Square(0.62, color=color, stroke_width=2, fill_color=fill or PAPER, fill_opacity=1 if fill else 0)


def pointer(color=BLU):
    tri = Triangle(color=color, fill_opacity=1, stroke_width=0).scale(0.16).rotate(PI)
    return VGroup(tri, T("p", 26, color, bold=True).next_to(tri, UP, 0.06))


def stop(text="Fil-C panic"):
    oct_ = RegularPolygon(8, color=ACC, fill_color=ACC, fill_opacity=1, stroke_width=0).scale(0.42).rotate(PI / 8)
    return VGroup(oct_, T("STOP", 18, PAPER, bold=True).move_to(oct_), T(text, 26, GRN, bold=True).next_to(oct_, RIGHT, 0.2))


class Explainer(Scene):
    cap = None

    def caption(self, s, color=INK, size=54):
        c = VGroup(*[T(line, size, color, bold=True) for line in s.split("\n")]).arrange(DOWN, buff=0.15)
        c.to_edge(UP, buff=0.5)
        if self.cap is None:
            self.play(FadeIn(c, shift=DOWN * 0.2), run_time=0.5)
        else:
            self.play(FadeOut(self.cap, shift=UP * 0.2), FadeIn(c, shift=UP * 0.2), run_time=0.5)
        self.cap = c

    def clear_all(self):
        self.play(*[FadeOut(m) for m in self.mobjects], run_time=0.5)
        self.cap = None

    def lanes(self):
        top = T("BIND", 34, MUTED, bold=True).move_to([-5.6, 0.9, 0])
        bot = T("Fil-BIND", 34, GRN, bold=True).move_to([-5.6, -1.9, 0])
        rule = DashedLine([-6.6, -0.5, 0], [6.6, -0.5, 0], color=FAINT, stroke_width=2)
        return top, bot, rule

    def construct(self):
        # 1. The news.
        cve = T("CVE-2026-94300", 120, ACC, bold=True)
        sub = T("BIND \\textperiodcentered{} memory corruption \\textperiodcentered{} potential remote code execution",
                36, INK).next_to(cve, DOWN, 0.45)
        when = T("ISC advisory, 21 October 2026", 28, MUTED).next_to(sub, DOWN, 0.3)
        self.play(FadeIn(cve, scale=0.9), run_time=0.8)
        self.play(FadeIn(sub), FadeIn(when))
        self.wait(1.6)
        self.play(FadeOut(cve), FadeOut(sub), FadeOut(when), run_time=0.5)

        # 2. Where it sits among this year's advisories.
        self.caption("37 BIND advisories since March")
        parts = [(6, "memory corruption", ACC), (11, "assertion exits", MUTED),
                 (12, "resource exhaustion", MUTED), (8, "logic, poisoning", MUTED)]
        unit, x = 12.0 / 37, -6.0
        segs, labs = VGroup(), VGroup()
        for n, name, color in parts:
            r = Rectangle(width=n * unit - 0.06, height=1.0, stroke_width=0, fill_color=color,
                          fill_opacity=1 if color == ACC else 0.35)
            r.move_to([x + n * unit / 2, 0, 0])
            segs.add(r)
            num = T(str(n), 48, PAPER if color == ACC else INK, bold=True).move_to(r)
            lab = T(name, 26, color if color == ACC else MUTED).next_to(r, DOWN, 0.25)
            labs.add(VGroup(num, lab))
            x += n * unit
        self.play(LaggedStart(*[GrowFromEdge(s, LEFT) for s in segs], lag_ratio=0.25), run_time=1.2)
        self.play(LaggedStart(*[FadeIn(l) for l in labs], lag_ratio=0.15), run_time=0.8)
        self.caption("6 are memory-safety bugs", ACC)
        self.play(segs[1:].animate.set_fill(opacity=0.12), labs[1:].animate.set_opacity(0.35),
                  Indicate(segs[0], color=ACC, scale_factor=1.05), run_time=0.8)
        self.wait(1.0)
        self.clear_all()

        # 3. Out of bounds: the write lands next door, or stops.
        self.caption("Write past the end")
        top, bot, rule = self.lanes()

        def row(y):
            buf = VGroup(*[cell() for _ in range(6)]).arrange(RIGHT, buff=0.06)
            key = VGroup(*[cell(AMB, "#f8e6cb") for _ in range(3)]).arrange(RIGHT, buff=0.06)
            VGroup(buf, key).arrange(RIGHT, buff=0.06).move_to([0.6, y, 0])
            bl = T("buffer", 24, MUTED).next_to(buf, DOWN, 0.15)
            kl = T("key", 24, AMB, bold=True).next_to(key, DOWN, 0.15)
            return buf, key, VGroup(bl, kl)

        b1, k1, l1 = row(0.9)
        b2, k2, l2 = row(-1.9)
        bounds = BraceBetweenPoints(b2.get_corner(UL) + UP * 0.12, b2.get_corner(UR) + UP * 0.12, UP, color=GRN)
        bl = T("p's bounds", 24, GRN, bold=True).next_to(bounds, UP, 0.05)
        self.play(FadeIn(top), FadeIn(bot), Create(rule), FadeIn(b1), FadeIn(k1), FadeIn(l1),
                  FadeIn(b2), FadeIn(k2), FadeIn(l2), run_time=0.6)
        p1 = pointer().next_to(b1[0], UP, 0.12)
        p2 = pointer().next_to(b2[0], UP, 0.12)
        self.play(FadeIn(p1), FadeIn(p2), GrowFromCenter(bounds), FadeIn(bl), run_time=0.5)
        self.play(FadeOut(bounds), FadeOut(bl), run_time=0.3)
        for i in range(6):
            self.play(p1.animate.next_to(b1[i], UP, 0.12), p2.animate.next_to(b2[i], UP, 0.12),
                      b1[i].animate.set_fill(BLU, 0.5), b2[i].animate.set_fill(BLU, 0.5), run_time=0.22)
        self.play(p1.animate.next_to(k1[0], UP, 0.12), p2.animate.next_to(k2[0], UP, 0.12), run_time=0.3)
        hit = T("key overwritten", 30, ACC, bold=True).next_to(k1, RIGHT, 0.35)
        st = stop().next_to(k2, RIGHT, 0.35)
        self.play(k1[0].animate.set_fill(ACC, 1).set_stroke(ACC), FadeIn(hit),
                  Indicate(k2[0], color=ACC), FadeIn(st, scale=0.8), run_time=0.7)
        self.wait(1.4)
        self.clear_all()

        # 4. Use after free: the pointer reads the next occupant, or stops.
        self.caption("Use after free")
        top, bot, rule = self.lanes()

        def obj(y, name, color):
            box = RoundedRectangle(corner_radius=0.12, width=2.8, height=1.0, color=color, stroke_width=3,
                                   fill_color=color, fill_opacity=0.15).move_to([0.6, y, 0])
            return VGroup(box, T(name, 32, color, bold=True).move_to(box))

        q1, q2 = obj(0.9, "query", BLU), obj(-1.9, "query", BLU)
        def side_pointer():
            tri = Triangle(color=BLU, fill_opacity=1, stroke_width=0).scale(0.16).rotate(-PI / 2)
            return VGroup(T("p", 26, BLU, bold=True), tri).arrange(RIGHT, buff=0.08)

        p1 = side_pointer().next_to(q1, LEFT, 0.3)
        p2 = side_pointer().next_to(q2, LEFT, 0.3)
        self.play(FadeIn(top), FadeIn(bot), Create(rule), FadeIn(q1), FadeIn(q2), FadeIn(p1), FadeIn(p2),
                  run_time=0.6)
        fr = M("free(query)", 30, MUTED).move_to([4.6, -0.5, 0])
        self.play(FadeIn(fr), run_time=0.3)
        key1 = obj(0.9, "TSIG key", AMB)
        freed = DashedVMobject(q2[0].copy().set_fill(opacity=0).set_stroke(FAINT), num_dashes=30)
        fl = T("freed", 30, MUTED).move_to(q2)
        self.play(ReplacementTransform(q1, key1), FadeOut(q2[0]), FadeOut(q2[1]), Create(freed), FadeIn(fl),
                  run_time=0.8)
        self.caption("Then reuse it")
        leak = T("reads the key", 30, ACC, bold=True).next_to(key1, RIGHT, 0.35)
        st = stop().next_to(freed, RIGHT, 0.35)
        self.play(p1.animate.shift(RIGHT * 0.25), p2.animate.shift(RIGHT * 0.25), run_time=0.3)
        self.play(Indicate(key1, color=ACC), FadeIn(leak), FadeIn(st, scale=0.8), run_time=0.7)
        self.wait(1.4)
        self.clear_all()

        # 5. What that buys, and what it does not.
        self.caption("Worst case: a crash", GRN)
        rce = T("remote code execution", 64, ACC, bold=True).move_to([0, 0.6, 0])
        self.play(FadeIn(rce))
        strike = Line(rce.get_left(), rce.get_right(), color=INK, stroke_width=6)
        dos = T("denial of service", 64, GRN, bold=True).move_to([0, -0.9, 0])
        self.play(Create(strike), run_time=0.4)
        self.play(FadeIn(dos, shift=UP * 0.2))
        self.wait(0.8)
        self.caption("Not a fix for the other 31", MUTED, 46)
        same = T("assertion exits still exit \\textperiodcentered{} floods still flood \\textperiodcentered{}"
                 " poisoning still poisons", 30, MUTED).move_to([0, -2.4, 0])
        self.play(FadeIn(same))
        self.wait(1.6)
        self.clear_all()

        # 6. It runs.
        self.caption("BIND 9.20.30 on Fil-C")
        items = [
            "BIND's unit tests pass",
            "DNSSEC-validating resolver",
            "AXFR, nsupdate, rndc",
            "image laid out like ISC's",
            f"about {SLOWDOWN}× slower",
        ]
        rows = VGroup()
        for i, s in enumerate(items):
            mark = T(r"{\fontspec{DejaVu Sans}" + ("✓" if i < 4 else "–") + "}", 40, GRN if i < 4 else MUTED, bold=True)
            rows.add(VGroup(mark, T(s, 40, INK if i < 4 else MUTED)).arrange(RIGHT, buff=0.35))
        rows.arrange(DOWN, aligned_edge=LEFT, buff=0.35).move_to([0, -0.4, 0])
        self.play(LaggedStart(*[FadeIn(r, shift=RIGHT * 0.2) for r in rows], lag_ratio=0.3), run_time=2.0)
        self.wait(1.4)
        self.clear_all()

        # 7. Where to get it.
        name = T("Fil-BIND", 120, GRN, bold=True).move_to([0, 1.3, 0])
        tag = T("a research build of BIND 9 in memory-safe C", 36, MUTED).next_to(name, DOWN, 0.35)
        pull = M("docker pull ghcr.io/mbrock/filnix-bind:9.20.30", 32, INK).move_to([0, -1.2, 0])
        url = T("mbrock.github.io/filnix/fil-bind", 34, ACC, bold=True).move_to([0, -2.4, 0])
        self.play(FadeIn(name, scale=0.9), run_time=0.7)
        self.play(FadeIn(tag))
        self.play(FadeIn(pull), FadeIn(url))
        self.wait(3.0)
