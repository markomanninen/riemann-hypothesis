"""Build the one-minute explainer of the redundancy check.

Usage: python3 verification/redundancy/explainer/build.py [stills]

The narration is spoken by the macOS voice Satu, one sentence of narration.json at a time, so
every picture starts exactly with its sentence. The pictures are drawn with matplotlib and
joined with ffmpeg. The result goes to ../data/explainer/, which git ignores: explainer.mp4,
captions.vtt and poster.jpg. With `stills` the script writes one frame per sentence instead.
"""
import glob, json, multiprocessing, os, subprocess, sys
import matplotlib as mpl
mpl.use("Agg")
import matplotlib.pyplot as plt, numpy as np
from matplotlib import font_manager as fm
from matplotlib.patches import FancyBboxPatch, Rectangle, FancyArrowPatch

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "data", "explainer")
for f in glob.glob(os.path.expanduser("~/Documents/GitHub/riemann/video/fonts/*.ttf")):
    fm.fontManager.addfont(f)
mpl.rcParams.update({"font.family": ["Inter", "DejaVu Sans"]})
MONO = ["DejaVu Sans Mono", "DejaVu Sans"]
FPS, W, H = 24, 12.8, 7.2
BG, INK, MUTED, FAINT, CARD = "#101418", "#EDE8DA", "#8C9199", "#2A313A", "#171C22"
BLUE, ORANGE, GREEN, RED, PURPLE = "#58C4DD", "#FFD866", "#7BD88F", "#FF7A6B", "#B79CF2"
VOICE, RATE, PAUSE, LEAD, TAIL = "Satu (Enhanced)", "200", 0.3, 0.4, 1.4
RNG = np.random.default_rng(3)
GX, GY = np.meshgrid(np.arange(113), np.arange(59))
DOTS = np.c_[GX.ravel(), GY.ravel()][:6667]            # one dot for 100 theorems
ORDER = RNG.permutation(len(DOTS))
CLUSTER = RNG.normal(0, 1, (156, 2))


def ease(u):
    u = np.clip(u, 0, 1)
    return u * u * (3 - 2 * u)


def ramp(u, a, b):
    return float(ease((u - a) / (b - a)))


def num(n):
    return f"{int(round(n)):,}".replace(",", " ")


def panel(ax, x, y, w, h, fc=CARD, ec=FAINT, alpha=1.0, lw=1.2, ls="-"):
    ax.add_patch(FancyBboxPatch((x, y), w, h, boxstyle="round,pad=0,rounding_size=0.12", fc=fc, ec=ec, lw=lw,
                                alpha=alpha, ls=ls))


def text(ax, x, y, s, size=20, color=INK, ha="left", va="center", alpha=1.0, mono=False, weight="normal"):
    kw = {"family": MONO} if mono else {}
    ax.text(x, y, s, fontsize=size, color=color, ha=ha, va=va, alpha=alpha, weight=weight, **kw)


def arrow(ax, a, b, color=MUTED, alpha=1.0, lw=2.0):
    ax.add_patch(FancyArrowPatch(a, b, arrowstyle="-|>", mutation_scale=18, color=color, lw=lw, alpha=alpha))


def dots(ax, shown, alpha=1.0):
    k = int(len(DOTS) * shown)
    p = DOTS[ORDER[:k]]
    ax.scatter(1.2 + p[:, 0] * 0.1205, 1.35 + p[:, 1] * 0.098, s=3.2, color=BLUE, alpha=alpha, linewidths=0)


def bar(ax, x, y, w, h, parts, total):
    """A bar of the given parts, each a (value, colour) pair, drawn to one scale."""
    panel(ax, x, y, w, h, fc=FAINT, ec="none")
    at = x
    for value, color in parts:
        ww = w * value / total
        if ww > 0:
            ax.add_patch(Rectangle((at, y), ww, h, color=color, lw=0))
        at += ww


def s1(ax, u):
    panel(ax, 0.9, 1.1, 14.2, 6.2)
    dots(ax, ramp(u, 0.05, 0.8))
    panel(ax, 4.6, 3.35, 6.8, 1.9, fc=BG, alpha=0.88)
    text(ax, 8, 4.6, num(666738 * ramp(u, 0.05, 0.8)), 46, ha="center", weight="bold")
    text(ax, 8, 3.78, "teoreemaa Lean-koodissa", 20, MUTED, ha="center")
    text(ax, 1.2, 0.72, "yksi piste on 100 teoreemaa", 14, MUTED)


def s2(ax, u):
    panel(ax, 0.9, 1.1, 14.2, 6.2)
    dots(ax, 1, alpha=1 - 0.75 * ramp(u, 0, 0.3))
    a = ramp(u, 0.1, 0.4)
    panel(ax, 3.2, 2.6, 9.6, 3.2, fc=BG, alpha=0.9 * a)
    for k, name in enumerate(("theorem a :", "theorem b :")):
        y = 4.9 - k * 1.1
        text(ax, 4.0, y, name, 26, INK, alpha=a, mono=True)
        text(ax, 8.9, y, "P", 30, ORANGE, alpha=a, mono=True, weight="bold")
    b = ramp(u, 0.45, 0.75)
    ax.plot([9.9, 10.2, 10.2, 9.9], [4.9, 4.9, 3.8, 3.8], color=ORANGE, lw=2, alpha=b)
    text(ax, 10.45, 4.35, "sama väite", 20, ORANGE, alpha=b)
    text(ax, 8, 2.95, "yksi jää, toinen on toisto", 17, MUTED, ha="center", alpha=b)
    text(ax, 1.2, 0.72, "kaksi nimeä, yksi väite", 14, MUTED, alpha=b)


def s3(ax, u):
    panel(ax, 0.9, 3.0, 6.6, 4.3)
    text(ax, 1.3, 6.75, "teoreema b", 14, MUTED)
    text(ax, 1.3, 5.9, "theorem b : P :=", 22, mono=True)
    text(ax, 1.9, 5.0, "a", 30, ORANGE, mono=True, weight="bold")
    text(ax, 1.3, 3.7, "koko todistus on yksi viittaus", 15, MUTED)
    panel(ax, 8.5, 3.0, 6.6, 4.3)
    text(ax, 8.9, 6.75, "teoreema a", 14, MUTED)
    text(ax, 8.9, 5.9, "theorem a : P := by", 22, mono=True)
    for k, wd in enumerate((4.6, 3.4, 5.2, 2.8)):
        ax.add_patch(Rectangle((9.5, 5.15 - k * 0.42), wd, 0.16, color=FAINT, lw=0))
    text(ax, 8.9, 3.4, "varsinainen todistus", 15, MUTED)
    a = ramp(u, 0.25, 0.5)
    arrow(ax, (2.5, 5.0), (8.4, 5.0), ORANGE, alpha=a)
    g = ramp(u, 0.4, 0.95)
    bar(ax, 0.9, 1.25, 14.2, 0.5, [(51364 * g, ORANGE)], 666738)
    text(ax, 0.9, 2.2, num(51364 * g), 30, ORANGE, weight="bold")
    text(ax, 3.9, 2.16, "teoreemaa viittaa toiseen", 18, MUTED)
    text(ax, 15.1, 0.85, "666 738", 13, MUTED, ha="right")
    text(ax, 0.9, 0.85, "0", 13, MUTED)


def two_files(ax, u_resolved=0.0, u_verdict=0.0):
    for k, (x, col, ns) in enumerate(((0.9, BLUE, "A"), (8.5, PURPLE, "B"))):
        panel(ax, x, 3.35, 6.6, 3.95)
        text(ax, x + 0.4, 6.8, f"tiedosto {k + 1}", 14, MUTED)
        text(ax, x + 0.4, 6.1, f"open {ns}", 20, col, mono=True)
        name = "spMap" if u_resolved < 0.5 else f"{ns}.spMap"
        fade = abs(2 * u_resolved - 1) if 0 < u_resolved < 1 else 1.0
        text(ax, x + 0.4, 5.1, f"{name} g ≫ {name} f", 19, col if u_resolved >= 0.5 else INK, mono=True, alpha=fade)
        text(ax, x + 0.4, 4.4, f"  = {name} (g.comp f)", 19, col if u_resolved >= 0.5 else INK, mono=True, alpha=fade)
        panel(ax, x + 0.9, 1.15, 4.8, 1.25, ec=col)
        text(ax, x + 3.3, 1.78, f"määritelmä {k + 1} nimelle spMap", 15, col, ha="center")
        arrow(ax, (x + 3.3, 3.3), (x + 3.3, 2.45), col)
    if u_verdict > 0:
        panel(ax, 7.55, 4.5, 0.9, 0.9, fc=BG, ec=RED, alpha=u_verdict)
        text(ax, 8, 4.93, "≠", 30, RED, ha="center", alpha=u_verdict, weight="bold")


def s4(ax, u):
    two_files(ax)
    a = ramp(u, 0.35, 0.7)
    text(ax, 8, 7.75, "sama teksti, kaksi eri määritelmää", 20, ORANGE, ha="center", alpha=a)


def s5(ax, u):
    two_files(ax, ramp(u, 0.15, 0.6), ramp(u, 0.7, 0.95))
    text(ax, 8, 7.75, "Lean kirjoittaa jokaisen nimen auki ja vertaa", 20, ORANGE, ha="center")


def pairs(ax, g, h):
    panel(ax, 0.9, 3.7, 14.2, 3.6)
    text(ax, 1.3, 6.75, "47 110 teoreemaa, jotka viittaavat toiseen ja jotka Lean vertasi", 15, MUTED)
    bar(ax, 1.3, 5.3, 13.4, 0.75, [(42737 * g, GREEN), (3706 * g, RED), (667 * g, MUTED)], 47110)
    text(ax, 1.3, 4.45, num(42737 * g), 34, GREEN, weight="bold")
    text(ax, 4.6, 4.4, "sama väite", 19, GREEN)
    text(ax, 14.7, 4.62, "3 706 eri väite", 15, RED, ha="right", alpha=g)
    text(ax, 14.7, 4.18, "667 vertaamatta", 15, MUTED, ha="right", alpha=g)
    panel(ax, 0.9, 1.1, 14.2, 2.2, alpha=0.35 + 0.65 * h)
    text(ax, 1.3, 2.75, "30 456 paria, joissa väitteen teksti on sama", 15, MUTED, alpha=0.35 + 0.65 * h)
    bar(ax, 1.3, 1.85, 13.4, 0.42, [(30157, GREEN), (170, RED), (129, MUTED)], 30456)
    if h > 0:
        arrow(ax, (14.3, 1.45), (14.56, 1.83), RED, alpha=h)
        text(ax, 14.2, 1.42, "170 parissa teksti on sama ja väite eri", 16, RED, ha="right", alpha=h)


def s6(ax, u):
    pairs(ax, ramp(u, 0.05, 0.55), ramp(u, 0.65, 0.9))


def s8(ax, u):
    panel(ax, 0.9, 1.1, 14.2, 6.2)
    m = ramp(u, 0.15, 0.6)
    kinds = [(141, GREEN, (4.6, 4.5), 0.75, "141 teoreemaa, yksi väite"), (5, PURPLE, (9.6, 5.9), 0.2, "5 teoreemaa, toinen väite"),
             (10, MUTED, (9.6, 4.3), 0.2, "10 yksityistä, vertaamatta")]
    at = 0
    for n, col, (cx, cy), spread, label in kinds:
        x0 = 4.6 + CLUSTER[at:at + n, 0] * 0.9
        y0 = 4.5 + CLUSTER[at:at + n, 1] * 0.7
        x1 = cx + CLUSTER[at:at + n, 0] * spread * 1.2
        y1 = cy + CLUSTER[at:at + n, 1] * spread
        ax.scatter(x0 + m * (x1 - x0), y0 + m * (y1 - y0), s=42, color=col if m > 0.5 else BLUE, linewidths=0)
        if n > 20:
            text(ax, 4.6, 1.75, label, 16, col, ha="center", alpha=ramp(u, 0.55, 0.75))
        else:
            text(ax, cx + 0.9, cy, label, 16, col, alpha=ramp(u, 0.55, 0.75))
        at += n
    text(ax, 1.3, 6.85, "156 teoreemaa, joiden väitteen teksti on sama", 15, MUTED)
    c = ramp(u, 0.6, 0.98)
    panel(ax, 8.9, 1.4, 6.0, 1.2, fc=BG)
    text(ax, 9.15, 2.0, num(50502 * c), 30, ORANGE, weight="bold")
    text(ax, 11.5, 1.95, "toistoa kaikissa ryhmissä", 14, MUTED)


def s9(ax, u):
    panel(ax, 0.9, 4.2, 14.2, 3.1)
    text(ax, 1.3, 6.75, "kaikki 666 738 teoreemaa", 15, MUTED)
    g = ramp(u, 0.05, 0.4)
    bar(ax, 1.3, 5.3, 13.4, 0.75, [(62905 * g, ORANGE)], 666738)
    text(ax, 1.3, 4.7, f"{num(62905 * g)} toistoa, 9,4 % teoreemoista", 17, ORANGE)
    a = ramp(u, 0.5, 0.75)
    panel(ax, 0.9, 1.1, 6.9, 2.7, ec=GREEN, alpha=a)
    text(ax, 1.3, 3.25, "koodin koko", 15, MUTED, alpha=a)
    text(ax, 1.3, 2.35, "pienenee, kun toistot poistetaan", 17, GREEN, alpha=a)
    panel(ax, 8.2, 1.1, 6.9, 2.7, ec=MUTED, alpha=a)
    text(ax, 8.6, 3.25, "todistuksen väitteet", 15, MUTED, alpha=a)
    text(ax, 8.6, 2.35, "pysyvät samoina, toisto ei lisää väitettä", 17, INK, alpha=a)


def s10(ax, u):
    panel(ax, 0.9, 2.6, 4.0, 3.2)
    text(ax, 2.9, 4.2, "koko koodi", 20, ha="center")
    panel(ax, 6.0, 2.6, 4.0, 3.2, ec=ORANGE, lw=2.2, ls="--")
    text(ax, 8.0, 4.5, "Leanin ydin", 20, ORANGE, ha="center")
    text(ax, 8.0, 3.75, "tarkistaa uudelleen", 14, MUTED, ha="center")
    text(ax, 8.0, 3.35, "jokaisen todistuksen", 14, MUTED, ha="center")
    panel(ax, 11.1, 2.6, 4.0, 3.2, ls="--")
    text(ax, 13.1, 4.2, "pätevä vai ei", 20, MUTED, ha="center")
    arrow(ax, (4.95, 4.2), (5.95, 4.2))
    arrow(ax, (10.05, 4.2), (11.05, 4.2), alpha=0.4)
    a = ramp(u, 0.3, 0.6)
    text(ax, 8.0, 1.75, "tätä ajoa en tehnyt", 22, ORANGE, ha="center", alpha=a, weight="bold")


def s11(ax, u):
    steps = ["poista yhden\nhakemiston toistot", "käännä\nkoko koodi", "kääntyy, siirry\nseuraavaan"]
    lit = min(2, int(u * 3.2))
    for k, label in enumerate(steps):
        x = 0.9 + k * 4.85
        on = k <= lit
        panel(ax, x, 3.0, 4.5, 2.6, ec=GREEN if on else FAINT, lw=2.2 if on else 1.2)
        text(ax, x + 2.25, 4.3, label, 19, INK if on else MUTED, ha="center")
        if k < 2:
            arrow(ax, (x + 4.52, 4.3), (x + 4.83, 4.3), GREEN if k < lit else MUTED)
    ax.plot([13.0, 13.0, 3.1, 3.1], [2.95, 2.1, 2.1, 2.9], color=MUTED, lw=2, alpha=ramp(u, 0.7, 0.9))
    arrow(ax, (3.1, 2.6), (3.1, 2.98), MUTED, alpha=ramp(u, 0.7, 0.9))
    text(ax, 8, 6.6, "ehdotus koodin ylläpitäjille", 20, ORANGE, ha="center")


SCENES = [s1, s2, s3, s4, s5, s6, s8, s9, s10, s11]


def spoken(sentence):
    """The sentence as the voice needs it: Lean by its sound, and a number it misreads in words."""
    return sentence.replace("Lean", "Liin").replace("50 502", "viisikymmentätuhatta viisisataakaksi")


def timeline():
    with open(os.path.join(HERE, "narration.json"), encoding="utf-8") as f:
        lines = json.load(f)
    at, out = LEAD, []
    for line in lines:
        wav = os.path.join(OUT, line["id"] + ".aiff")
        subprocess.run(["say", "-v", VOICE, "-r", RATE, "-o", wav, spoken(line["text"])], check=True)
        d = float(subprocess.run(["ffprobe", "-v", "error", "-show_entries", "format=duration", "-of", "csv=p=0", wav],
                                 capture_output=True, text=True).stdout)
        out.append({"id": line["id"], "text": line["text"], "start": at, "end": at + d, "wav": wav})
        at += d + PAUSE
    return out, at - PAUSE + TAIL


def frame(job):
    path, scene, u = job
    fig = plt.figure(figsize=(W, H), dpi=100)
    ax = fig.add_axes([0, 0, 1, 1])
    ax.set_xlim(0, 16); ax.set_ylim(0, 9); ax.axis("off")
    ax.add_patch(Rectangle((0, 0), 16, 9, color=BG, zorder=-10))
    text(ax, 0.9, 8.42, "TOISTUVAT TEOREEMAT  ·  TEKSTIHAKU JA LEANIN VERTAILU", 11, MUTED)
    SCENES[scene](ax, u)
    fig.savefig(path, facecolor=BG)
    plt.close(fig)


def stamp(t):
    return f"{int(t // 3600):02d}:{int(t % 3600 // 60):02d}:{t % 60:06.3f}"


def main():
    os.makedirs(os.path.join(OUT, "frames"), exist_ok=True)
    cues, total = timeline()
    if "stills" in sys.argv:
        for k in range(len(SCENES)):
            frame((os.path.join(OUT, f"still_{k + 1:02d}.png"), k, 0.97))
        return
    jobs = []
    for n in range(int(total * FPS)):
        t = n / FPS
        k = max(i for i, c in enumerate(cues) if c["start"] - (LEAD if i == 0 else PAUSE / 2) <= t or i == 0)
        c = cues[k]
        u = (t - c["start"]) / (c["end"] - c["start"])
        jobs.append((os.path.join(OUT, "frames", f"{n:05d}.png"), k, float(np.clip(u, 0, 1))))
    with multiprocessing.get_context("fork").Pool() as pool:
        pool.map(frame, jobs, chunksize=8)
    inputs, filters = [], []
    for i, c in enumerate(cues):
        inputs += ["-i", c["wav"]]
        filters.append(f"[{i + 1}:a]adelay={int(c['start'] * 1000)}:all=1[a{i}]")
    mix = "".join(f"[a{i}]" for i in range(len(cues)))
    graph = ";".join(filters) + f";{mix}amix=inputs={len(cues)}:normalize=0,apad=whole_dur={total:.3f}[a]"
    video = os.path.join(OUT, "explainer.mp4")
    subprocess.run(["ffmpeg", "-v", "error", "-y", "-framerate", str(FPS), "-i", os.path.join(OUT, "frames", "%05d.png"),
                    *inputs, "-filter_complex", graph, "-map", "0:v", "-map", "[a]", "-c:v", "libx264", "-pix_fmt",
                    "yuv420p", "-crf", "20", "-c:a", "aac", "-b:a", "128k", "-t", f"{total:.3f}", "-movflags",
                    "+faststart", video], check=True)
    with open(os.path.join(OUT, "captions.vtt"), "w", encoding="utf-8") as f:
        f.write("WEBVTT\n\n")
        for c in cues:
            f.write(f"{stamp(c['start'])} --> {stamp(c['end'])}\n{c['text']}\n\n")
    frame((os.path.join(OUT, "poster.png"), 5, 1.0))  # the picture of the confirmed pairs
    subprocess.run(["ffmpeg", "-v", "error", "-y", "-i", os.path.join(OUT, "poster.png"), "-q:v", "3",
                    os.path.join(OUT, "poster.jpg")], check=True)
    for p in glob.glob(os.path.join(OUT, "frames", "*.png")):
        os.remove(p)
    print(f"{video}  {total:.1f} s")


if __name__ == "__main__":
    main()
