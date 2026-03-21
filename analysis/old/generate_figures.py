"""
Reproducible figure generation for:
  "Cohesion-Sensitive Power Indices" (Working Paper, v9)

Generates three figures:
  1. Apex game sensitivity (Figure 1 / fig:sensitivity)
  2. Bundestag Scenario A — Pure Ideology (left panel of fig:bundestag_comparison)
  3. Bundestag Scenario B — Cordon Sanitaire (right panel of fig:bundestag_comparison)

Each figure is produced in two style variants:
  - "academic"  : minimal, journal-ready (thin lines, muted palette, LaTeX labels)
  - "polished"  : modern seaborn-style with refined palette

Usage:
  python generate_figures.py              # generates all figures in both styles
  python generate_figures.py --style academic
  python generate_figures.py --style polished
"""

import argparse
import os
from math import factorial
from itertools import combinations
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.ticker as ticker

# ---------------------------------------------------------------------------
# Core computation
# ---------------------------------------------------------------------------

def shapley_size_weight(k, n):
    """Standard Shapley size weight: k!(n-k-1)!/n!"""
    return factorial(k) * factorial(n - k - 1) / factorial(n)


def cohesion_shapley(players, weights, threshold, kappa_func, b_val):
    """
    Compute the normalised Cohesion-Shapley index for a weighted majority game.

    Parameters
    ----------
    players : list
        Player labels.
    weights : dict
        {player: seat_count}.
    threshold : int
        Majority threshold (strict: > or >=, here >= following paper convention > half).
    kappa_func : callable
        kappa_func(frozenset) -> float.  Cohesion of a coalition.
    b_val : float
        Cohesion exponent.

    Returns
    -------
    dict  {player: normalised_phi}
    """
    n = len(players)
    others_of = {p: [q for q in players if q != p] for p in players}

    def coalition_weight(S):
        return sum(weights[p] for p in S)

    def is_winning(S):
        return coalition_weight(S) >= threshold

    raw_phi = {}
    for i in players:
        others = others_of[i]
        m = len(others)  # n-1
        numerator = 0.0
        denominator = 0.0
        # iterate over all subsets S ⊆ N\{i}
        for r in range(m + 1):
            omega_r = shapley_size_weight(r, n)
            for combo in combinations(others, r):
                S = frozenset(combo)
                S_plus_i = S | {i}
                kap = kappa_func(S_plus_i)
                kap_b = kap ** b_val if kap > 0 else 0.0
                term = omega_r * kap_b
                denominator += term
                # marginal contribution: i pivotal?
                if is_winning(S_plus_i) and not is_winning(S):
                    numerator += term
        raw_phi[i] = numerator / denominator if denominator > 0 else 0.0

    # normalise so values sum to 1
    total = sum(raw_phi.values())
    if total > 0:
        return {p: raw_phi[p] / total for p in players}
    else:
        return {p: 0.0 for p in players}


# ---------------------------------------------------------------------------
# Figure 1: Apex game
# ---------------------------------------------------------------------------

APEX_PLAYERS = ["A", "B", "C"]
APEX_WEIGHTS = {"A": 45, "B": 35, "C": 20}
APEX_THRESHOLD = 51  # majority of 100

# Cohesion structure (directly specified in the paper caption)
APEX_KAPPA_PAIRS = {
    frozenset({"A", "B"}): 0.20,
    frozenset({"A", "C"}): 0.05,
    frozenset({"B", "C"}): 0.90,
}
# Grand coalition: driven by max distance (A–C pair), so same as κ({A,C})
APEX_KAPPA_GRAND = 0.05


def apex_kappa(S):
    if len(S) <= 1:
        return 1.0
    S = frozenset(S)
    if len(S) == 2:
        return APEX_KAPPA_PAIRS.get(S, 0.0)
    if len(S) == 3:
        return APEX_KAPPA_GRAND
    return 0.0


def compute_apex_data(b_values):
    results = {p: [] for p in APEX_PLAYERS}
    for b in b_values:
        phi = cohesion_shapley(APEX_PLAYERS, APEX_WEIGHTS, APEX_THRESHOLD,
                               apex_kappa, b)
        for p in APEX_PLAYERS:
            results[p].append(phi[p])
    return results


# ---------------------------------------------------------------------------
# Figures 2–3: Bundestag
# ---------------------------------------------------------------------------

BT_PLAYERS = ["CDU/CSU", "AfD", "SPD", "Grüne", "Linke"]
BT_WEIGHTS = {"CDU/CSU": 208, "AfD": 152, "SPD": 120, "Grüne": 85, "Linke": 64}
BT_THRESHOLD = 316  # > half of 630

# CHES left-right positions
BT_POSITIONS = {
    "CDU/CSU": 6.5,
    "AfD": 9.0,
    "SPD": 3.5,
    "Grüne": 3.8,
    "Linke": 1.8,
}


def bt_kappa_ideology(S):
    """κ(S) = (1 + max_{i,j ∈ S} |λ_i − λ_j|)^{−1}, singletons → 1."""
    S = frozenset(S)
    if len(S) <= 1:
        return 1.0
    positions = [BT_POSITIONS[p] for p in S]
    max_range = max(positions) - min(positions)
    return 1.0 / (1.0 + max_range)


def bt_kappa_cordon(S):
    """Scenario B: κ(S) = 0 for all S ∋ AfD with |S| ≥ 2."""
    S = frozenset(S)
    if len(S) <= 1:
        return 1.0
    if "AfD" in S and len(S) >= 2:
        return 0.0
    positions = [BT_POSITIONS[p] for p in S]
    max_range = max(positions) - min(positions)
    return 1.0 / (1.0 + max_range)


def compute_bundestag_data(b_values, kappa_func):
    results = {p: [] for p in BT_PLAYERS}
    for b in b_values:
        phi = cohesion_shapley(BT_PLAYERS, BT_WEIGHTS, BT_THRESHOLD,
                               kappa_func, b)
        for p in BT_PLAYERS:
            results[p].append(phi[p])
    return results


# ---------------------------------------------------------------------------
# Styling presets
# ---------------------------------------------------------------------------

def setup_style_academic():
    """Minimal, journal-ready style. LaTeX-rendered labels, muted palette."""
    plt.rcParams.update({
        "font.family": "serif",
        "font.size": 10,
        "axes.linewidth": 0.6,
        "axes.edgecolor": "#333333",
        "axes.labelsize": 11,
        "axes.titlesize": 12,
        "xtick.major.width": 0.5,
        "ytick.major.width": 0.5,
        "xtick.direction": "in",
        "ytick.direction": "in",
        "xtick.major.size": 3,
        "ytick.major.size": 3,
        "legend.fontsize": 9,
        "legend.frameon": True,
        "legend.edgecolor": "#cccccc",
        "legend.fancybox": False,
        "figure.dpi": 300,
        "savefig.dpi": 300,
        "savefig.bbox": "tight",
        "savefig.pad_inches": 0.05,
    })
    plt.rcParams["text.usetex"] = False
    # Note: set text.usetex = True if a full LaTeX installation is available


# Muted academic palette (colorblind-friendly, works in grayscale)
ACADEMIC_COLORS_APEX = {
    "A": "#2166ac",   # steel blue
    "B": "#b2182b",   # brick red
    "C": "#4d9221",   # olive green
}
ACADEMIC_COLORS_BT = {
    "CDU/CSU": "#1a1a1a",  # near-black
    "AfD":     "#2166ac",  # blue
    "SPD":     "#b2182b",  # red
    "Grüne":   "#4d9221",  # green
    "Linke":   "#7b3294",  # purple
}
ACADEMIC_LW = 1.4
ACADEMIC_DASH = (5, 3)


def setup_style_polished():
    """Modern, polished seaborn-inspired style."""
    plt.rcParams.update({
        "font.family": "sans-serif",
        "font.sans-serif": ["Helvetica", "DejaVu Sans", "Arial"],
        "font.size": 11,
        "axes.linewidth": 0.8,
        "axes.edgecolor": "#4a4a4a",
        "axes.labelsize": 12,
        "axes.titlesize": 13,
        "axes.facecolor": "#fafafa",
        "xtick.major.width": 0.6,
        "ytick.major.width": 0.6,
        "xtick.direction": "out",
        "ytick.direction": "out",
        "xtick.major.size": 4,
        "ytick.major.size": 4,
        "legend.fontsize": 10,
        "legend.frameon": True,
        "legend.edgecolor": "#dddddd",
        "legend.fancybox": True,
        "legend.shadow": False,
        "figure.dpi": 300,
        "savefig.dpi": 300,
        "savefig.bbox": "tight",
        "savefig.pad_inches": 0.08,
        "text.usetex": False,
        "grid.alpha": 0.3,
        "grid.linewidth": 0.5,
    })


# Polished palette — vivid but tasteful
POLISHED_COLORS_APEX = {
    "A": "#3b82f6",  # bright blue
    "B": "#ef4444",  # red
    "C": "#22c55e",  # green
}
POLISHED_COLORS_BT = {
    "CDU/CSU": "#1e293b",  # slate-900
    "AfD":     "#3b82f6",  # blue-500
    "SPD":     "#ef4444",  # red-500
    "Grüne":   "#22c55e",  # green-500
    "Linke":   "#a855f7",  # purple-500
}
POLISHED_LW = 2.0
POLISHED_DASH = (6, 3)


# ---------------------------------------------------------------------------
# Plotting functions
# ---------------------------------------------------------------------------

def plot_apex(b_values, data, style, outpath):
    if style == "academic":
        setup_style_academic()
        colors = ACADEMIC_COLORS_APEX
        lw = ACADEMIC_LW
        dash = ACADEMIC_DASH
    else:
        setup_style_polished()
        colors = POLISHED_COLORS_APEX
        lw = POLISHED_LW
        dash = POLISHED_DASH

    fig, ax = plt.subplots(figsize=(6.5, 4.2))

    labels = {
        "A": "Party A (45%, isolated)",
        "B": "Party B (35%, bridge)",
        "C": "Party C (20%, partner)",
    }
    for p in ["A", "B", "C"]:
        ax.plot(b_values, data[p], color=colors[p], linewidth=lw, label=labels[p])

    ax.axvline(x=1, color="#888888", linestyle="--", linewidth=0.8,
               dashes=dash, label=r"$b = 1$" if style == "academic" else "b = 1")

    ax.set_xlabel(r"Cohesion exponent $b$" if style == "academic"
                  else "Cohesion exponent b")
    ax.set_ylabel(r"Normalised power index $\Phi$" if style == "academic"
                  else "Normalised power index Φ")
    if style == "polished":
        ax.set_title("Effect of cohesion parameter b on power distribution",
                     fontweight="medium", pad=10)
        ax.grid(True, alpha=0.3)

    ax.set_xlim(0, 4)
    ax.set_ylim(-0.02, 0.58)
    ax.yaxis.set_major_locator(ticker.MultipleLocator(0.1))
    ax.legend(loc="center right", framealpha=0.95)

    fig.savefig(outpath)
    plt.close(fig)
    print(f"  → {outpath}")


def plot_bundestag(b_values, data_a, data_b, style, outpath):
    if style == "academic":
        setup_style_academic()
        colors = ACADEMIC_COLORS_BT
        lw = ACADEMIC_LW
        dash = ACADEMIC_DASH
    else:
        setup_style_polished()
        colors = POLISHED_COLORS_BT
        lw = POLISHED_LW
        dash = POLISHED_DASH

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12.5, 4.8), sharey=True)

    for ax, data, title_suffix in [
        (ax1, data_a, "Pure Ideology (No Cordon)"),
        (ax2, data_b, "Cordon Sanitaire against AfD"),
    ]:
        for p in BT_PLAYERS:
            ax.plot(b_values, data[p], color=colors[p], linewidth=lw, label=p)
        ax.axvline(x=1, color="#888888", linestyle="--", linewidth=0.8,
                   dashes=dash)

        if style == "academic":
            ax.set_title(f"Scenario {'A' if 'Pure' in title_suffix else 'B'}: "
                         f"{title_suffix}",
                         fontsize=10, pad=8)
        else:
            ax.set_title(f"Scenario {'A' if 'Pure' in title_suffix else 'B'}: "
                         f"{title_suffix}",
                         fontweight="medium", fontsize=11, pad=10)
            ax.grid(True, alpha=0.3)

        ax.set_xlabel(r"Cohesion exponent $b$" if style == "academic"
                      else "Cohesion exponent b")
        ax.set_xlim(0, 3)

    ax1.set_ylabel(r"Power index $\Phi$" if style == "academic"
                   else "Power index Φ")
    ax1.set_ylim(-0.02, 0.72)
    ax1.yaxis.set_major_locator(ticker.MultipleLocator(0.1))

    # Add subtitle
    if style == "academic":
        fig.suptitle(
            "21st German Bundestag — official result, 23 February 2025",
            fontsize=10, y=1.01, fontstyle="italic"
        )
    else:
        fig.suptitle(
            "21st German Bundestag — official result, 23 February 2025",
            fontsize=11.5, y=1.02, fontweight="medium"
        )

    # Shared legend below
    handles, labels = ax1.get_legend_handles_labels()
    # Add the b=1 line to legend
    from matplotlib.lines import Line2D
    handles.append(Line2D([0], [0], color="#888888", linestyle="--",
                          linewidth=0.8))
    labels.append(r"$b = 1$" if style == "academic" else "b = 1")
    fig.legend(handles, labels, loc="lower center", ncol=6,
               bbox_to_anchor=(0.5, -0.06), frameon=True,
               edgecolor="#cccccc")

    fig.tight_layout()
    fig.savefig(outpath)
    plt.close(fig)
    print(f"  → {outpath}")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description="Generate paper figures.")
    parser.add_argument("--style", choices=["academic", "polished", "both"],
                        default="both",
                        help="Figure style variant (default: both)")
    args = parser.parse_args()

    styles = ["academic", "polished"] if args.style == "both" else [args.style]
    outdir = os.path.dirname(os.path.abspath(__file__))

    # Compute data (shared across styles)
    print("Computing Apex game data …")
    b_apex = np.linspace(0.001, 4.0, 300)
    apex_data = compute_apex_data(b_apex)

    print("Computing Bundestag Scenario A (pure ideology) …")
    b_bt = np.linspace(0.001, 3.0, 200)
    bt_data_a = compute_bundestag_data(b_bt, bt_kappa_ideology)

    print("Computing Bundestag Scenario B (cordon sanitaire) …")
    bt_data_b = compute_bundestag_data(b_bt, bt_kappa_cordon)

    for style in styles:
        print(f"\nGenerating [{style}] figures:")
        suffix = f"_{style}"

        plot_apex(b_apex, apex_data, style,
                  os.path.join(outdir, f"fig1_apex{suffix}.pdf"))
        plot_bundestag(b_bt, bt_data_a, bt_data_b, style,
                       os.path.join(outdir, f"fig2_bundestag{suffix}.pdf"))

    # Also save PNG versions for quick preview
    for style in styles:
        print(f"\nGenerating [{style}] PNG previews:")
        suffix = f"_{style}"
        plot_apex(b_apex, apex_data, style,
                  os.path.join(outdir, f"fig1_apex{suffix}.png"))
        plot_bundestag(b_bt, bt_data_a, bt_data_b, style,
                       os.path.join(outdir, f"fig2_bundestag{suffix}.png"))

    print("\nDone.")


if __name__ == "__main__":
    main()
