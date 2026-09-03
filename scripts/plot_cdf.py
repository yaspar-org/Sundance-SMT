#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

"""Plot solve-time CDFs for several run_verus.py log files on one chart.

Each log contains lines of the form

    [1/5630] nice-split/nice/cvc5/abstract_machine_state.1.smt2 -> UNSAT [1.31s]

Lines without ``->`` are ignored. For every line whose result matches the
selected status (UNSAT by default), the trailing ``[<time>s]`` field is
collected; the plot then shows, for each log, how many benchmarks were solved
within a given amount of time.
"""

import argparse
import re
import sys
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

# Colorblind friendly color pallete
SERIES_COLORS = ["#2a78d6", "#eb6834", "#1baf7a", "#4a3aa7"]
SURFACE = "#fcfcfb"
TEXT_PRIMARY = "#0b0b0b"
TEXT_SECONDARY = "#52514e"
TEXT_MUTED = "#6f6e6a"
GRID = "#e3e2dd"

# For example: -> UNSAT [1.31s]
RESULT_RE = re.compile(r"->\s*(\S+)\s*\[\s*([0-9.]+)\s*s\s*\]\s*$")
# For example: [1.06s]
PROGRESS_RE = re.compile(r"^\[\s*\d+\s*/\s*(\d+)\s*\]")


def parse_log(path, status):
    """Return the `status` solve times (seconds) in `path` and the benchmark total.

    The total comes from the `[i/N]` progress prefix; if no line carries one it
    falls back to the number of result lines seen.
    """
    times = []
    total = 0
    results = 0
    skipped = 0
    with open(path) as f:
        for line in f:
            if "->" not in line:
                continue
            line = line.rstrip()
            m = RESULT_RE.search(line)
            if m is None:
                skipped += 1
                continue
            results += 1
            p = PROGRESS_RE.match(line)
            if p is not None:
                total = max(total, int(p.group(1)))
            if m.group(1) == status:
                times.append(float(m.group(2)))
    if skipped:
        print(f"{path}: {skipped} arrow line(s) without a parsable time", file=sys.stderr)
    times.sort()
    return times, max(total, results)


def place_labels(ys, min_gap):
    """Nudge label positions apart, preserving order, to avoid collisions."""
    order = sorted(range(len(ys)), key=lambda i: ys[i])
    placed = list(ys)
    prev = None
    for i in order:
        if prev is not None and placed[i] - prev < min_gap:
            placed[i] = prev + min_gap
        prev = placed[i]
    return placed


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("logs", nargs="+", help="log files produced by run_verus.py")
    ap.add_argument("-o", "--output", default="cdf.png", help="output image (default: cdf.png)")
    ap.add_argument("--status", default="UNSAT", help="result status to count (default: UNSAT)")
    ap.add_argument("--xmax", type=float, default=10.0, help="x-axis upper bound in seconds (default: 10)")
    ap.add_argument("--title", default=None, help="chart title")
    ap.add_argument("--dpi", type=int, default=200, help="output resolution (default: 200)")
    args = ap.parse_args()

    if len(args.logs) > len(SERIES_COLORS):
        ap.error(f"at most {len(SERIES_COLORS)} logs can be plotted together")

    series = []
    for path in args.logs:
        times, total = parse_log(path, args.status)
        if not times:
            print(f"{path}: no {args.status} results found - skipping", file=sys.stderr)
            continue
        label = Path(path).stem
        series.append((label, times, total))
        within = sum(1 for t in times if t <= args.xmax)
        print(f"{label}: {len(times)}/{total} {args.status} ({100 * len(times) / total:.1f}%), "
              f"{within} within {args.xmax:g}s, "
              f"median {times[len(times) // 2]:.2f}s, max {times[-1]:.2f}s", file=sys.stderr)

    if not series:
        sys.exit("nothing to plot")

    fig, ax = plt.subplots(figsize=(9, 5.5), facecolor=SURFACE)
    ax.set_facecolor(SURFACE)

    ends = []
    for (label, times, total), color in zip(series, SERIES_COLORS):
        # Step function: at time t the count is the number of times <= t.
        xs = [0.0] + times
        ys = list(range(len(times) + 1))
        ax.step(xs, ys, where="post", color=color, linewidth=2, label=label,
                solid_capstyle="round", clip_on=True)
        ends.append((label, color, sum(1 for t in times if t <= args.xmax), total))

    ymax = max(y for _, _, y, _ in ends)
    ax.set_xlim(0, args.xmax)
    ax.set_ylim(0, ymax * 1.06)

    # Direct labels at the right edge, nudged apart where lines end close together.
    label_ys = place_labels([y for _, _, y, _ in ends], min_gap=ymax * 0.055)
    for (label, color, y, total), ly in zip(ends, label_ys):
        ax.annotate(f"{label}  {y}  ({100 * y / total:.1f}%)", xy=(args.xmax, ly), xytext=(8, 0),
                    textcoords="offset points", va="center", ha="left",
                    fontsize=9, color=TEXT_SECONDARY, annotation_clip=False)
        ax.plot([args.xmax], [y], marker="o", markersize=5, color=color,
                markeredgecolor=SURFACE, markeredgewidth=1.5, clip_on=False)

    ax.set_xlabel("solve time (s)", fontsize=10, color=TEXT_SECONDARY)
    ax.set_ylabel(f"benchmarks solved ({args.status})", fontsize=10, color=TEXT_SECONDARY)
    ax.set_title(args.title or f"{args.status} benchmarks solved within a time budget",
                 fontsize=13, color=TEXT_PRIMARY, loc="left", pad=12)

    ax.grid(True, axis="y", color=GRID, linewidth=0.8)
    ax.set_axisbelow(True)
    for side in ("top", "right"):
        ax.spines[side].set_visible(False)
    for side in ("left", "bottom"):
        ax.spines[side].set_color(GRID)
    ax.tick_params(colors=TEXT_MUTED, labelsize=9, length=0)

    legend = ax.legend(loc="lower right", frameon=False, fontsize=9)
    for text in legend.get_texts():
        text.set_color(TEXT_SECONDARY)

    fig.subplots_adjust(right=0.67, left=0.09, top=0.9, bottom=0.11)
    fig.savefig(args.output, dpi=args.dpi, facecolor=SURFACE)
    print(f"wrote {args.output}", file=sys.stderr)


if __name__ == "__main__":
    main()
