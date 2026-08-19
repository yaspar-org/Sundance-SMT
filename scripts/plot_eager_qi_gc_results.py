#!/usr/bin/env python3
"""Plot and summarize the eager-QI garbage-collection benchmark matrix."""

from __future__ import annotations

import argparse
import csv
import math
from collections import Counter
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


MODES = (0, 20, 50, -1)
COLORS = {
    0: "#2a78d6",
    20: "#eb6834",
    50: "#1baf7a",
    -1: "#b04a8b",
}
STATUS_COLORS = {
    "both_unsat": ("#2a78d6", "both UNSAT"),
    "baseline_only": ("#eb6834", "only baseline UNSAT"),
    "variant_only": ("#1baf7a", "only variant UNSAT"),
    "neither": ("#898781", "neither UNSAT"),
}
SURFACE = "#fcfcfb"
INK = "#0b0b0b"
INK2 = "#52514e"
MUTED = "#898781"
GRID = "#e1e0d9"
BASELINE = "#c3c2b7"

STAT_FIELDS = (
    ("time_seconds", "Wall-clock time (s)", 0.01),
    ("solve_time", "Internal solve time (s)", 0.01),
    ("decisions", "SAT decisions", 1.0),
    ("backtracks", "Backtracks", 1.0),
    ("conflicts", "Theory conflicts", 1.0),
    ("arith_checks", "Arithmetic checks", 1.0),
    ("instantiations", "Quantifier instantiations", 1.0),
    ("instantiation_rounds", "Instantiation rounds", 1.0),
    ("egraph_merges", "E-graph merges", 1.0),
    ("bool_vars", "Boolean variables", 1.0),
    ("total_clauses", "Clauses created", 1.0),
    ("deleted_clauses", "Clauses deleted", 1.0),
    ("qi_gc_cycles", "QI GC cycles", 1.0),
    ("qi_instances_retired", "QI instances retired", 1.0),
    ("qi_instances_retained", "QI instances retained", 1.0),
    ("qi_clauses_retired", "QI clauses retired", 1.0),
    ("qi_gc_fallbacks", "QI GC fallbacks", 1.0),
)


def style_axis(axis):
    axis.set_facecolor(SURFACE)
    axis.spines["top"].set_visible(False)
    axis.spines["right"].set_visible(False)
    for side in ("left", "bottom"):
        axis.spines[side].set_color(BASELINE)
    axis.tick_params(colors=MUTED, labelsize=8, length=3, width=0.8)
    axis.grid(True, color=GRID, linewidth=0.7)
    axis.set_axisbelow(True)
    axis.xaxis.label.set_color(INK2)
    axis.yaxis.label.set_color(INK2)


def save_figure(figure, output_prefix):
    output_prefix.parent.mkdir(parents=True, exist_ok=True)
    for suffix in (".png", ".pdf"):
        figure.savefig(
            output_prefix.with_suffix(suffix),
            dpi=180 if suffix == ".png" else None,
            facecolor=SURFACE,
            bbox_inches="tight",
        )
    plt.close(figure)


def run_key(path):
    name = path.name
    gc_enabled = "-qi-gc-" in name
    if "eager-qi--1-" in name:
        mode = -1
    else:
        mode = next(
            (candidate for candidate in (0, 20, 50) if f"eager-qi-{candidate}-" in name),
            None,
        )
    if mode is None:
        raise RuntimeError(f"cannot identify eager-QI mode from {path}")
    return mode, gc_enabled


def label(key):
    mode, gc_enabled = key
    mode_label = "q=full" if mode == -1 else f"q={mode}"
    return f"{mode_label}, GC {'on' if gc_enabled else 'off'}"


def parse_number(value):
    if value is None or not value.strip():
        return None
    try:
        number = float(value)
    except ValueError:
        return None
    return number if math.isfinite(number) else None


def load_run(path):
    results = {}
    with path.open(newline="") as stream:
        for row in csv.DictReader(stream):
            query = row["file"]
            if query in results:
                raise RuntimeError(f"duplicate query in {path}: {query}")
            parsed = {
                key: parse_number(row.get(key))
                for key, _, _ in STAT_FIELDS
                if key != "total_clauses"
            }
            clauses = parse_number(row.get("clauses"))
            binary = parse_number(row.get("binary_clauses"))
            parsed["total_clauses"] = (
                clauses + binary if clauses is not None and binary is not None else None
            )
            parsed["status"] = row["result"].strip().lower()
            results[query] = parsed
    return results


def discover_runs(results_dir):
    runs = {}
    for path in sorted(results_dir.glob("*_results.csv")):
        key = run_key(path)
        if key in runs:
            raise RuntimeError(f"duplicate run for {label(key)}: {runs[key][0]} and {path}")
        runs[key] = (path, load_run(path))

    expected = {(mode, gc_enabled) for mode in MODES for gc_enabled in (False, True)}
    missing = expected - set(runs)
    extra = set(runs) - expected
    if missing or extra:
        raise RuntimeError(f"run matrix mismatch: missing={missing}, extra={extra}")

    query_sets = {frozenset(results) for _, results in runs.values()}
    if len(query_sets) != 1:
        raise RuntimeError("runs do not contain identical benchmark query sets")
    return runs


def unsat_times(results):
    return np.sort(
        np.asarray(
            [
                result["time_seconds"]
                for result in results.values()
                if result["status"] == "unsat" and result["time_seconds"] is not None
            ],
            dtype=float,
        )
    )


def plot_cdf(runs, keys, output_prefix, title):
    total = len(runs[keys[0]][1])
    common_unsat = set.intersection(
        *[
            {
                query
                for query, result in runs[key][1].items()
                if result["status"] == "unsat"
            }
            for key in keys
        ]
    )

    figure, axes = plt.subplots(1, 2, figsize=(17, 7.2))
    figure.patch.set_facecolor(SURFACE)
    for key in keys:
        mode, gc_enabled = key
        results = runs[key][1]
        times = unsat_times(results)
        percentages = np.arange(1, len(times) + 1) / total * 100
        line_style = "--" if gc_enabled else "-"
        axes[0].step(
            times,
            percentages,
            where="post",
            color=COLORS[mode],
            linestyle=line_style,
            linewidth=1.9,
            label=f"{label(key)} ({len(times)} UNSAT)",
        )

        common_times = np.sort(
            np.asarray([results[query]["time_seconds"] for query in common_unsat])
        )
        common_percentages = (
            np.arange(1, len(common_times) + 1) / len(common_times) * 100
        )
        axes[1].step(
            common_times,
            common_percentages,
            where="post",
            color=COLORS[mode],
            linestyle=line_style,
            linewidth=1.9,
            label=label(key),
        )

    axes[0].set_title("All benchmarks", color=INK, fontweight="bold")
    axes[0].set_ylabel(f"Percent of all {total:,} queries proved UNSAT")
    axes[0].legend(loc="upper left", fontsize=8, framealpha=0.95)
    axes[1].set_title(
        f"Common UNSAT cohort ({len(common_unsat):,} queries)",
        color=INK,
        fontweight="bold",
    )
    axes[1].set_ylabel("Percent of common cohort solved")
    axes[1].legend(loc="lower right", fontsize=8, framealpha=0.95)

    for axis in axes:
        style_axis(axis)
        axis.set_xscale("log")
        axis.set_xlim(left=0.01, right=70)
        axis.set_xlabel("Per-query wall-clock time (s, log scale)")
        axis.axvline(60, color=MUTED, linestyle=(0, (4, 3)), linewidth=1)

    figure.suptitle(title, fontsize=15, color=INK, fontweight="bold")
    figure.tight_layout(rect=(0, 0, 1, 0.95))
    save_figure(figure, output_prefix)


def status_category(baseline, variant):
    baseline_unsat = baseline["status"] == "unsat"
    variant_unsat = variant["status"] == "unsat"
    if baseline_unsat and variant_unsat:
        return "both_unsat"
    if baseline_unsat:
        return "baseline_only"
    if variant_unsat:
        return "variant_only"
    return "neither"


def metric_vectors(baseline, variant, field):
    queries = [
        query
        for query in sorted(set(baseline) & set(variant))
        if baseline[query].get(field) is not None and variant[query].get(field) is not None
    ]
    x_values = np.asarray([baseline[query][field] for query in queries], dtype=float)
    y_values = np.asarray([variant[query][field] for query in queries], dtype=float)
    categories = [status_category(baseline[query], variant[query]) for query in queries]
    return queries, x_values, y_values, categories


def comparison_fields(baseline, variant):
    fields = []
    for field, title, linear_threshold in STAT_FIELDS:
        _, x_values, y_values, _ = metric_vectors(baseline, variant, field)
        if not len(x_values):
            continue
        if np.all(x_values == 0) and np.all(y_values == 0):
            continue
        fields.append((field, title, linear_threshold))
    return fields


def plot_runtime_scatter(runs, baseline_key, variant_key, output_prefix):
    baseline = runs[baseline_key][1]
    variant = runs[variant_key][1]
    _, x_values, y_values, categories = metric_vectors(
        baseline, variant, "time_seconds"
    )

    figure, axis = plt.subplots(figsize=(8.2, 7.5))
    figure.patch.set_facecolor(SURFACE)
    style_axis(axis)
    for category, (color, category_label) in STATUS_COLORS.items():
        mask = np.asarray([value == category for value in categories])
        if np.any(mask):
            axis.scatter(
                x_values[mask],
                y_values[mask],
                color=color,
                alpha=0.35,
                s=12,
                edgecolors="none",
                label=f"{category_label} ({int(mask.sum())})",
            )

    lower = max(min(x_values.min(), y_values.min()) * 0.8, 0.005)
    upper = max(x_values.max(), y_values.max()) * 1.2
    axis.plot(
        [lower, upper],
        [lower, upper],
        color=BASELINE,
        linestyle=(0, (4, 3)),
        linewidth=1.2,
    )
    axis.set_xscale("log")
    axis.set_yscale("log")
    axis.set_xlim(lower, upper)
    axis.set_ylim(lower, upper)
    axis.set_aspect("equal", adjustable="box")
    axis.set_xlabel(f"{label(baseline_key)} wall time (s)")
    axis.set_ylabel(f"{label(variant_key)} wall time (s)")
    axis.set_title(
        f"Runtime: {label(variant_key)} vs {label(baseline_key)}",
        color=INK,
        fontweight="bold",
    )
    axis.legend(loc="lower right", fontsize=8, framealpha=0.95)
    figure.tight_layout()
    save_figure(figure, output_prefix)


def ratio_text(y_values, x_values):
    x_total = float(x_values.sum())
    y_total = float(y_values.sum())
    if x_total == 0:
        return "new activity" if y_total else "both zero"
    return f"aggregate ratio {y_total / x_total:.2f}x"


def plot_stats_scatter(runs, baseline_key, variant_key, output_prefix):
    baseline = runs[baseline_key][1]
    variant = runs[variant_key][1]
    fields = comparison_fields(baseline, variant)
    columns = 4
    rows = math.ceil(len(fields) / columns)
    figure, axes = plt.subplots(rows, columns, figsize=(18, 4.3 * rows))
    figure.patch.set_facecolor(SURFACE)
    axes = np.atleast_1d(axes).flatten()

    for index, (field, title, linear_threshold) in enumerate(fields):
        axis = axes[index]
        style_axis(axis)
        _, x_values, y_values, categories = metric_vectors(
            baseline, variant, field
        )
        for category, (color, category_label) in STATUS_COLORS.items():
            mask = np.asarray([value == category for value in categories])
            if np.any(mask):
                axis.scatter(
                    x_values[mask],
                    y_values[mask],
                    color=color,
                    alpha=0.3,
                    s=9,
                    edgecolors="none",
                    label=category_label,
                    rasterized=True,
                )

        upper = max(float(x_values.max()), float(y_values.max()), linear_threshold)
        upper *= 1.12
        lower = 0.0
        axis.plot(
            [lower, upper],
            [lower, upper],
            color=BASELINE,
            linestyle=(0, (4, 3)),
            linewidth=1,
        )
        if field in ("time_seconds", "solve_time"):
            positive = np.concatenate((x_values[x_values > 0], y_values[y_values > 0]))
            lower = max(float(positive.min()) * 0.8, 0.001)
            axis.set_xscale("log")
            axis.set_yscale("log")
        else:
            axis.set_xscale("symlog", linthresh=linear_threshold)
            axis.set_yscale("symlog", linthresh=linear_threshold)
        axis.set_xlim(lower, upper)
        axis.set_ylim(lower, upper)
        axis.set_aspect("equal", adjustable="box")
        axis.set_title(
            f"{title}\n{ratio_text(y_values, x_values)}",
            fontsize=10,
            color=INK,
            fontweight="bold",
        )
        axis.set_xlabel(label(baseline_key), fontsize=8)
        axis.set_ylabel(label(variant_key), fontsize=8)

    for axis in axes[len(fields) :]:
        axis.axis("off")

    handles = [
        plt.Line2D(
            [],
            [],
            marker="o",
            linestyle="",
            color=color,
            label=category_label,
            markersize=6,
        )
        for color, category_label in STATUS_COLORS.values()
    ]
    figure.legend(handles=handles, loc="lower center", ncol=4, fontsize=9)
    figure.suptitle(
        f"Per-query statistics: {label(variant_key)} (Y) vs "
        f"{label(baseline_key)} (X)",
        fontsize=14,
        color=INK,
        fontweight="bold",
    )
    figure.tight_layout(rect=(0, 0.035, 1, 0.965))
    save_figure(figure, output_prefix)


def geometric_mean(values):
    values = np.asarray([value for value in values if value > 0], dtype=float)
    if not len(values):
        return None
    return float(np.exp(np.mean(np.log(values))))


def write_summaries(runs, output_dir):
    rows = []
    for key in [(mode, gc) for gc in (False, True) for mode in MODES]:
        results = runs[key][1]
        counts = Counter(result["status"] for result in results.values())
        times = [
            result["time_seconds"]
            for result in results.values()
            if result["status"] == "unsat"
        ]
        rows.append(
            {
                "configuration": label(key),
                "unsat": counts["unsat"],
                "timeout": counts["timeout"],
                "unknown": counts["unknown"],
                "error": counts["error"],
                "other": counts["other"],
                "median_unsat_time": float(np.median(times)),
                "total_qi_gc_cycles": sum(
                    result.get("qi_gc_cycles") or 0 for result in results.values()
                ),
                "total_qi_instances_retired": sum(
                    result.get("qi_instances_retired") or 0
                    for result in results.values()
                ),
                "total_qi_instances_retained": sum(
                    result.get("qi_instances_retained") or 0
                    for result in results.values()
                ),
            }
        )

    summary_csv = output_dir / "benchmark_summary.csv"
    with summary_csv.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)

    comparison_rows = []
    comparisons = []
    for gc_enabled in (False, True):
        comparisons.extend([((0, gc_enabled), (mode, gc_enabled)) for mode in (20, 50, -1)])
    comparisons.extend([((mode, False), (mode, True)) for mode in MODES])
    for baseline_key, variant_key in comparisons:
        baseline = runs[baseline_key][1]
        variant = runs[variant_key][1]
        common_unsat = [
            query
            for query in baseline
            if baseline[query]["status"] == "unsat"
            and variant[query]["status"] == "unsat"
        ]
        ratios = [
            variant[query]["time_seconds"] / baseline[query]["time_seconds"]
            for query in common_unsat
        ]
        baseline_unsat = sum(result["status"] == "unsat" for result in baseline.values())
        variant_unsat = sum(result["status"] == "unsat" for result in variant.values())
        comparison_rows.append(
            {
                "baseline": label(baseline_key),
                "variant": label(variant_key),
                "baseline_unsat": baseline_unsat,
                "variant_unsat": variant_unsat,
                "unsat_delta": variant_unsat - baseline_unsat,
                "common_unsat": len(common_unsat),
                "runtime_geomean_ratio_variant_over_baseline": geometric_mean(ratios),
            }
        )

    comparison_csv = output_dir / "comparison_summary.csv"
    with comparison_csv.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(comparison_rows[0]))
        writer.writeheader()
        writer.writerows(comparison_rows)

    markdown = output_dir / "benchmark_summary.md"
    with markdown.open("w") as stream:
        stream.write("# Eager-QI Garbage Collection Benchmark\n\n")
        stream.write(
            "| Configuration | UNSAT | Timeout | Unknown | Error | Other | "
            "Median UNSAT time | GC cycles |\n"
        )
        stream.write("|---|---:|---:|---:|---:|---:|---:|---:|\n")
        for row in rows:
            stream.write(
                f"| {row['configuration']} | {row['unsat']} | {row['timeout']} "
                f"| {row['unknown']} | {row['error']} | {row['other']} "
                f"| {row['median_unsat_time']:.3f}s "
                f"| {row['total_qi_gc_cycles']:.0f} |\n"
            )
        stream.write("\n## Pairwise Comparisons\n\n")
        stream.write("| Baseline | Variant | UNSAT delta | Common UNSAT | Runtime geometric-mean ratio |\n")
        stream.write("|---|---|---:|---:|---:|\n")
        for row in comparison_rows:
            stream.write(
                f"| {row['baseline']} | {row['variant']} "
                f"| {row['unsat_delta']:+d} | {row['common_unsat']} "
                f"| {row['runtime_geomean_ratio_variant_over_baseline']:.3f}x |\n"
            )


def comparison_slug(baseline_key, variant_key):
    baseline_mode, baseline_gc = baseline_key
    variant_mode, variant_gc = variant_key
    mode_name = lambda mode: "full" if mode == -1 else str(mode)
    return (
        f"q{mode_name(baseline_mode)}_{'gc' if baseline_gc else 'no_gc'}"
        f"_vs_q{mode_name(variant_mode)}_{'gc' if variant_gc else 'no_gc'}"
    )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("results_dir", type=Path)
    parser.add_argument("output_dir", type=Path)
    args = parser.parse_args()

    runs = discover_runs(args.results_dir)
    args.output_dir.mkdir(parents=True, exist_ok=True)

    all_keys = [(mode, gc) for gc in (False, True) for mode in MODES]
    plot_cdf(
        runs,
        all_keys,
        args.output_dir / "cdf_all_eight_configurations",
        "UFDTLIA: Eager-QI and Root-Level QI Garbage Collection",
    )
    plot_cdf(
        runs,
        [(mode, False) for mode in MODES],
        args.output_dir / "cdf_gc_off",
        "UFDTLIA: Eager-QI Configurations, Garbage Collection Off",
    )
    plot_cdf(
        runs,
        [(mode, True) for mode in MODES],
        args.output_dir / "cdf_gc_on",
        "UFDTLIA: Eager-QI Configurations, Garbage Collection On",
    )

    comparisons = []
    for gc_enabled in (False, True):
        comparisons.extend([((0, gc_enabled), (mode, gc_enabled)) for mode in (20, 50, -1)])
    comparisons.extend([((mode, False), (mode, True)) for mode in MODES])
    for baseline_key, variant_key in comparisons:
        slug = comparison_slug(baseline_key, variant_key)
        plot_runtime_scatter(
            runs,
            baseline_key,
            variant_key,
            args.output_dir / f"runtime_{slug}",
        )
        plot_stats_scatter(
            runs,
            baseline_key,
            variant_key,
            args.output_dir / f"stats_{slug}",
        )

    write_summaries(runs, args.output_dir)
    print(f"wrote plots and summaries to {args.output_dir}")


if __name__ == "__main__":
    main()
