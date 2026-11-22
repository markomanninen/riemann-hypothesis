#!/usr/bin/env python3
"""Render a tour of the proof explorer into a video file.

Usage: python3 -I verification/explorer/record_tour.py tours/longest-chain.json [options]

The script serves the explorer on a local port, opens the page in Chrome on a stage of the
chosen size, and lets the page draw the tour frame by frame. The page sends every frame back
as raw pixels, and ffmpeg packs them into an MP4 file. A frame is drawn for its own moment of
the tour, so the video runs at an even speed however long a frame takes to draw.

Needs Google Chrome and ffmpeg. ANIMATIONS.md describes tour files and the options here.
"""
import argparse
import http.server
import os
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import urllib.parse

HERE = os.path.dirname(os.path.abspath(__file__))
CHROMES = ["/Applications/Google Chrome.app/Contents/MacOS/Google Chrome", "google-chrome", "chromium", "chrome"]


class Job:
    """The state of one recording, shared between the server threads and the main thread."""

    def __init__(self, width, height, fps, out, crf):
        self.size, self.frames, self.total, self.error = width * height * 4, 0, 0, None
        self.finished, self.last = threading.Event(), time.time()
        self.ffmpeg = subprocess.Popen(
            ["ffmpeg", "-loglevel", "error", "-y", "-f", "rawvideo", "-pix_fmt", "rgba", "-s", f"{width}x{height}",
             "-framerate", str(fps), "-i", "-", "-c:v", "libx264", "-preset", "medium", "-crf", str(crf),
             "-pix_fmt", "yuv420p", "-movflags", "+faststart", out], stdin=subprocess.PIPE)

    def fail(self, message):
        self.error = self.error or message
        self.finished.set()


def handler(job):
    class Handler(http.server.SimpleHTTPRequestHandler):
        protocol_version = "HTTP/1.1"

        def __init__(self, *args, **kwargs):
            super().__init__(*args, directory=HERE, **kwargs)

        def log_message(self, *args):
            pass

        def do_POST(self):
            url = urllib.parse.urlparse(self.path)
            body = self.rfile.read(int(self.headers.get("Content-Length", 0)))
            job.last = time.time()
            if url.path == "/begin":
                job.total = int(urllib.parse.parse_qs(url.query).get("frames", ["0"])[0])
            elif url.path == "/frame":
                if len(body) != job.size:
                    job.fail(f"a frame has {len(body)} bytes and the stage needs {job.size}")
                else:
                    try:
                        job.ffmpeg.stdin.write(body)
                        job.frames += 1
                    except BrokenPipeError:
                        job.fail("ffmpeg stopped taking frames")
            elif url.path == "/done":
                job.finished.set()
            elif url.path == "/fail":
                job.fail(body.decode("utf-8", "replace"))
            self.send_response(204)
            self.send_header("Content-Length", "0")
            self.end_headers()

    return Handler


def main():
    ap = argparse.ArgumentParser(description="Render a tour of the proof explorer into a video file.")
    ap.add_argument("tour", help="tour file, as a path below verification/explorer, such as tours/longest-chain.json")
    ap.add_argument("--size", default="1920x1080", help="frame size in pixels (default 1920x1080)")
    ap.add_argument("--scale", type=int, default=2, help="pixels per unit of layout, 2 for 1080p and 4 for 2160p (default 2)")
    ap.add_argument("--fps", type=int, default=30, help="frames per second (default 30)")
    ap.add_argument("--from", dest="start", type=float, default=0, help="first second of the tour to render")
    ap.add_argument("--to", dest="end", type=float, help="last second of the tour to render")
    ap.add_argument("--out", help="video file to write (default clips/<tour name>.mp4)")
    ap.add_argument("--crf", type=int, default=18, help="x264 quality, lower is better and larger (default 18)")
    ap.add_argument("--window", action="store_true", help="show the Chrome window while it draws")
    args = ap.parse_args()

    width, height = (int(v) for v in args.size.lower().split("x"))
    if width % (2 * args.scale) or height % (2 * args.scale):
        sys.exit(f"The size {args.size} has to divide evenly by twice the scale, {2 * args.scale}.")
    tour = os.path.relpath(os.path.abspath(os.path.join(HERE, args.tour) if not os.path.exists(args.tour) else args.tour), HERE)
    if tour.startswith("..") or not os.path.exists(os.path.join(HERE, tour)):
        sys.exit(f"The tour file {args.tour} was not found below {HERE}.")
    chrome = next((c for c in CHROMES if os.path.exists(c) or shutil.which(c)), None)
    if not chrome or not shutil.which("ffmpeg"):
        sys.exit("Recording needs Google Chrome and ffmpeg on this machine.")
    out = os.path.abspath(args.out or os.path.join(HERE, "clips", os.path.splitext(os.path.basename(tour))[0] + ".mp4"))
    os.makedirs(os.path.dirname(out), exist_ok=True)

    job = Job(width, height, args.fps, out, args.crf)
    server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), handler(job))
    threading.Thread(target=server.serve_forever, daemon=True).start()
    query = {"stage": args.size, "scale": args.scale, "tour": tour.replace(os.sep, "/"), "record": 1, "fps": args.fps, "from": args.start}
    if args.end is not None:
        query["to"] = args.end
    url = f"http://127.0.0.1:{server.server_address[1]}/index.html?" + urllib.parse.urlencode(query)
    profile = tempfile.mkdtemp(prefix="record-tour-")
    flags = [f"--user-data-dir={profile}", "--no-first-run", "--no-default-browser-check", "--mute-audio", "--hide-scrollbars",
             f"--window-size={width // args.scale},{height // args.scale}", "--disable-background-timer-throttling",
             "--disable-renderer-backgrounding", "--disable-backgrounding-occluded-windows"]
    if not args.window:
        flags += ["--headless=new", "--enable-gpu", "--use-angle=metal" if sys.platform == "darwin" else "--use-angle=default"]
    browser = subprocess.Popen([chrome, *flags, url], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    started = time.time()
    try:
        while not job.finished.wait(0.5):
            if job.total:
                sys.stderr.write(f"\rframe {job.frames} of {job.total}")
            if browser.poll() is not None:
                job.fail("Chrome closed before the tour ended")
            elif time.time() - job.last > 180:
                job.fail("the page sent nothing for three minutes")
    except KeyboardInterrupt:
        job.fail("stopped from the keyboard")
    finally:
        sys.stderr.write("\n")
        browser.terminate()
        try:
            browser.wait(10)
        except subprocess.TimeoutExpired:
            browser.kill()
        server.shutdown()
        job.ffmpeg.stdin.close()
        job.ffmpeg.wait()
        shutil.rmtree(profile, ignore_errors=True)
    if job.error:
        if os.path.exists(out) and not job.frames:
            os.remove(out)
        hint = "" if args.window else " Run it again with --window to see the page while it draws."
        sys.exit(f"The recording failed, because {job.error}.{hint}")
    print(f"{out}: {job.frames} frames, {job.frames / args.fps:.1f} s at {args.fps} frames a second, "
          f"{os.path.getsize(out) / 1e6:.1f} MB, drawn in {time.time() - started:.0f} s")


if __name__ == "__main__":
    main()
