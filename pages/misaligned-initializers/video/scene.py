"""A short explainer for misaligned pointers in Fil-C global and TLS initializers.

Render with ./render.sh, which writes ../explainer.mp4 and ../poster.png.

Captions are a few words each, so the pictures carry the argument and the
page has the details. All text goes through XeLaTeX in Public Sans, the
wiki's font, for proper kerning.
"""

import os

from manim import *

PAPER = "#ffffff"
INK = "#111111"
MUTED = "#667078"
ACC = "#9a3248"  # the wiki's accent: the bug
AMB = "#d98a1c"  # plain bytes
BLU = "#2f6fb3"  # pointer bytes and capabilities
GRN = "#3d7a3d"  # the fix

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

CELL = 0.36  # one byte
X0 = -2.9  # left edge of byte 0


def T(s, size=30, color=INK, bold=False):
    return Tex(r"\textbf{" + s + "}" if bold else s, tex_template=TPL, font_size=size, color=color)


def M(s, size=26, color=INK):
    s = s.replace("\\", r"\textbackslash{}").replace("_", r"\_").replace("&", r"\&").replace("%", r"\%")
    s = s.replace("{", r"\{").replace("}", r"\}").replace(r"\textbackslash\{\}", r"\textbackslash{}")
    return Tex(r"\texttt{" + s + "}", tex_template=TPL, font_size=size, color=color)


def bx(i):
    return X0 + CELL * (i + 0.5)


def byte_row(y, n=16, label=None):
    cells = VGroup(*[Square(CELL, color=MUTED, stroke_width=1.5).move_to([bx(i), y, 0]) for i in range(n)])
    words = VGroup(*[
        Rectangle(width=CELL * 8, height=CELL + 0.12, color=INK, stroke_width=3).move_to([bx(8 * w + 3.5), y, 0])
        for w in range(n // 8)
    ])
    g = VGroup(cells, words)
    if label:
        g.add(T(label, 22, MUTED).next_to(words, LEFT, 0.25))
    return g


def span(i0, n, y, color, opacity=0.85):
    return Rectangle(width=CELL * n, height=CELL - 0.06, stroke_width=0, fill_color=color,
                     fill_opacity=opacity).move_to([bx(i0 + (n - 1) / 2), y, 0])


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
        # 1. The hook: an ordinary-looking packed initializer.
        code = VGroup(
            M("struct __attribute__((packed)) P {", 24),
            M("  char c;", 24),
            M("  int *p;", 24, BLU),
            M("};", 24),
            M("_Thread_local struct P t = { 1, &x };", 24),
        ).arrange(DOWN, buff=0.12, aligned_edge=LEFT).move_to([0, 0.2, 0])
        # Alignment uses visible glyphs, so indent the member lines by hand.
        em = M("xx", 24).width
        code[1].shift(RIGHT * em)
        code[2].shift(RIGHT * em)
        self.caption("A pointer at byte 1")
        self.play(FadeIn(code), run_time=0.6)
        self.play(Indicate(code[2], color=BLU, scale_factor=1.1), run_time=0.8)
        self.wait(1.0)
        self.play(FadeOut(code), run_time=0.4)

        # 2. Fil-C keeps one capability per word, in a shadow word.
        self.caption("Each word has a shadow")
        obj = byte_row(0.9, label="object")
        sh = byte_row(-1.1, label="shadow")
        wl = VGroup(T("word 0", 20, MUTED).next_to(obj[1][0], UP, 0.1),
                    T("word 1", 20, MUTED).next_to(obj[1][1], UP, 0.1))
        self.play(FadeIn(obj), FadeIn(sh), FadeIn(wl), run_time=0.6)
        ptr = span(0, 8, 0.9, BLU)
        cap = span(0, 8, -1.1, BLU, 0.5)
        cl = T("capability", 22, BLU, bold=True).move_to(cap)
        arrow = Arrow(ptr.get_bottom(), cap.get_top(), color=BLU, buff=0.12, stroke_width=4)
        self.play(FadeIn(ptr), run_time=0.4)
        self.play(GrowArrow(arrow), FadeIn(cap), FadeIn(cl), run_time=0.6)
        self.caption("One pointer, one shadow word")
        self.wait(1.2)

        # 3. Packed: the pointer straddles two words.
        self.caption("Packed: it straddles two", ACC)
        c0 = span(0, 1, 0.9, AMB)
        ptr2 = span(1, 8, 0.9, BLU)
        self.play(FadeOut(arrow), FadeOut(cap), FadeOut(cl), Transform(ptr, ptr2), FadeIn(c0), run_time=0.8)
        q = T("?", 64, ACC, bold=True).move_to([0, -1.1, 0])
        self.play(FadeIn(q, scale=0.8), Indicate(sh[1], color=ACC), run_time=0.8)
        self.caption("No shadow word fits", ACC)
        self.wait(1.0)
        self.play(FadeOut(q), run_time=0.3)

        # 4. Globals: the compiler assertion.
        self.caption("Global: clang aborts", ACC)
        msg = VGroup(M("Assertion `!(Offset % WordSize)' failed.", 22, ACC),
                     M("clang frontend command failed", 22, ACC)).arrange(DOWN, buff=0.1, aligned_edge=LEFT)
        msg.move_to([0, -2.7, 0])
        self.play(FadeIn(msg, shift=UP * 0.2), run_time=0.5)
        self.wait(1.8)
        self.play(FadeOut(msg), run_time=0.3)

        # 5. Thread-locals: an unchecked store smears the capability.
        self.caption("Thread-local: no check", ACC)
        bad = span(1, 8, -1.1, ACC, 0.6)
        arr2 = Arrow(ptr.get_bottom(), bad.get_top(), color=ACC, buff=0.12, stroke_width=4)
        self.play(GrowArrow(arr2), FadeIn(bad), run_time=0.7)
        ir = M("store ptr %lower, ptr (aux + 1), align 8", 22, ACC).move_to([0, -2.5, 0])
        self.play(FadeIn(ir), run_time=0.4)
        self.caption("Capability smeared\nacross two shadows", ACC)
        self.wait(1.4)

        # 6. Word 0's shadow is now garbage.
        self.caption("Read word 0", ACC)
        self.play(FadeOut(ir), FadeOut(arr2), run_time=0.3)
        hl = SurroundingRectangle(VGroup(obj[1][0], sh[1][0]), color=ACC, buff=0.12, stroke_width=4)
        self.play(Create(hl), run_time=0.5)
        seg = T("Segmentation fault", 50, ACC, bold=True).move_to([0, -2.5, 0])
        no = T("no Fil-C error", 28, MUTED).next_to(seg, DOWN, 0.15)
        self.play(FadeIn(seg, scale=1.1), run_time=0.4)
        self.play(FadeIn(no), run_time=0.4)
        self.wait(1.8)
        self.clear_all()

        # 7. The fix: refuse at compile time.
        self.caption("Fix: refuse at compile time", GRN)
        err = VGroup(
            M("error: Fil-C cannot initialize 't':", 24, GRN),
            M("a pointer in its initializer", 24, GRN),
            M("is not word-aligned", 24, GRN),
        ).arrange(DOWN, buff=0.1, aligned_edge=LEFT).move_to([0, 0.9, 0])
        self.play(FadeIn(err, shift=UP * 0.2), run_time=0.6)
        ok = VGroup(
            T("Pointers on word boundaries: unchanged", 30, INK),
            T("All-zero initializers: unchanged", 30, INK),
            T("Reads and writes: still checked", 30, INK),
        ).arrange(DOWN, buff=0.25, aligned_edge=LEFT).move_to([0, -1.4, 0])
        self.play(LaggedStart(*[FadeIn(o, shift=RIGHT * 0.2) for o in ok], lag_ratio=0.5), run_time=1.6)
        self.wait(1.6)
        url = T("mbrock.github.io/filnix/misaligned-initializers", 24, ACC).move_to([0, -3.3, 0])
        self.play(FadeIn(url))
        self.wait(2.5)
