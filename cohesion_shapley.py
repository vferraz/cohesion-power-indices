"""
Cohesion-sensitive power indices: corrected core functions.

Implements the normalised cohesion-Shapley index (Definition 4.9) and
the normalised cohesion-Banzhaf index (Definition 3.2) as specified in

    "Cohesion-Sensitive Power Indices: Representation Results
     for Banzhaf and Shapley Values"

The key formula (Theorem 4.5, Shapley branch) is:

    p_i^κ(S) = α_{|S|} · κ(S∪{i})^b  /  Σ_T α_{|T|} · κ(T∪{i})^b

    F_i = Σ_{S⊆N∖{i}} p_i^κ(S) · Δ_i v(S)

    Φ_i = F_i / Σ_j F_j · v(N)

The Banzhaf branch (Theorem 3.7) replaces the Shapley size weights
α_k = k!(n−k−1)!/n!  with the uniform weight  1/2^{n−1}.
"""

import math
from itertools import combinations


# ------------------------------------------------------------------ #
#  Size weights                                                       #
# ------------------------------------------------------------------ #

def shapley_size_weight(k, n):
    """Shapley size weight: α_k = k!(n-k-1)!/n!"""
    if k < 0 or k >= n:
        return 0.0
    return math.factorial(k) * math.factorial(n - k - 1) / math.factorial(n)


def banzhaf_size_weight(k, n):
    """Banzhaf size weight: 1/2^{n-1} (uniform over all coalitions)."""
    if k < 0 or k >= n:
        return 0.0
    return 1.0 / (2 ** (n - 1))


# ------------------------------------------------------------------ #
#  Generic cohesion-weighted value (covers both branches)             #
# ------------------------------------------------------------------ #

def cohesion_value(players, weights, threshold, kappa_func, b,
                   size_weight_func=shapley_size_weight):
    """
    Compute the normalised cohesion-sensitive power index.

    Parameters
    ----------
    players : list
        Player identifiers (e.g. party names).
    weights : dict
        Maps each player to its seat count.
    threshold : int or float
        A coalition S is winning iff sum of weights >= threshold.
    kappa_func : callable
        kappa_func(coalition_frozenset) -> float in [0, 1].
        Receives a frozenset of player identifiers.
        Must return 1.0 for singletons.
    b : float
        Cohesion exponent (b > 0).
    size_weight_func : callable, optional
        size_weight_func(k, n) -> float.  Defaults to Shapley weights.
        Pass banzhaf_size_weight for the Banzhaf branch.

    Returns
    -------
    dict  {player: Φ_i}   with  Σ_i Φ_i = 1  (for non-degenerate games).
    """
    n = len(players)
    F = {}                       # unnormalised values

    for player_i in players:
        others = [p for p in players if p != player_i]

        # --- denominator  D_i = Σ_T α_{|T|} · κ(T∪{i})^b  ----------
        D_i = 0.0
        for r in range(len(others) + 1):
            for subset in combinations(others, r):
                S = frozenset(subset)
                alpha = size_weight_func(len(S), n)
                kappa = kappa_func(S | {player_i})
                D_i += alpha * (kappa ** b)

        # --- numerator  F_i = Σ_{S: pivotal} p_i(S)  ----------------
        F_i = 0.0
        for r in range(len(others) + 1):
            for subset in combinations(others, r):
                S = frozenset(subset)
                alpha = size_weight_func(len(S), n)
                kappa = kappa_func(S | {player_i})

                # Luce-normalised probability
                p = (alpha * (kappa ** b) / D_i) if D_i > 0 else 0.0

                # pivotality:  S loses, S∪{i} wins
                w_S = sum(weights[q] for q in S)
                if (w_S < threshold) and (w_S + weights[player_i] >= threshold):
                    F_i += p

        F[player_i] = F_i

    # --- efficiency normalisation:  Φ_i = F_i / Σ_j F_j  -----------
    #     (v(N) = 1 for simple games)
    total = sum(F.values())
    if total > 0:
        return {p: F[p] / total for p in players}
    return {p: 0.0 for p in players}


# ------------------------------------------------------------------ #
#  Convenience wrappers                                               #
# ------------------------------------------------------------------ #

def cohesion_shapley(players, weights, threshold, kappa_func, b):
    """Normalised cohesion-Shapley index  Φ  (Definition 4.9)."""
    return cohesion_value(players, weights, threshold, kappa_func, b,
                          size_weight_func=shapley_size_weight)


def cohesion_banzhaf(players, weights, threshold, kappa_func, b):
    """Normalised cohesion-Banzhaf index  B  (Definition 3.2)."""
    return cohesion_value(players, weights, threshold, kappa_func, b,
                          size_weight_func=banzhaf_size_weight)


# ------------------------------------------------------------------ #
#  Self-test (run with  python cohesion_shapley.py)                   #
# ------------------------------------------------------------------ #

if __name__ == "__main__":
    import numpy as np

    # --- Apex game from the paper -----------------------------------
    players = ['A', 'B', 'C']
    weights = {'A': 45, 'B': 35, 'C': 20}
    threshold = 51
    cohesion_table = {
        frozenset({'A', 'B'}): 0.20,
        frozenset({'A', 'C'}): 0.05,
        frozenset({'B', 'C'}): 0.90,
        frozenset({'A', 'B', 'C'}): 0.05,
    }

    def kappa(S):
        key = frozenset(S)
        return cohesion_table.get(key, 1.0)

    def kappa_one(S):
        return 1.0

    # Test 1: cohesionless benchmark must recover classical Shapley
    phi0 = cohesion_shapley(players, weights, threshold, kappa_one, 1.0)
    assert abs(phi0['A'] - 1/3) < 1e-10, f"Shapley benchmark failed: {phi0}"
    assert abs(phi0['B'] - 1/3) < 1e-10
    assert abs(phi0['C'] - 1/3) < 1e-10
    print("PASS  cohesionless benchmark recovers classical Shapley (1/3 each)")

    # Test 2: normalisation
    for b in [0.5, 1.0, 2.0, 3.0]:
        phi = cohesion_shapley(players, weights, threshold, kappa, b)
        s = sum(phi.values())
        assert abs(s - 1.0) < 1e-10, f"Sum != 1 at b={b}: {s}"
    print("PASS  index sums to 1 for all tested b values")

    # Test 3: cohesion monotonicity — B and C (high cohesion pair)
    # should gain power as b increases
    phi_low = cohesion_shapley(players, weights, threshold, kappa, 0.1)
    phi_high = cohesion_shapley(players, weights, threshold, kappa, 3.0)
    assert phi_high['B'] > phi_low['B'], "B should gain power as b rises"
    assert phi_high['A'] < phi_low['A'], "A should lose power as b rises"
    print("PASS  cohesion monotonicity: B gains, A loses as b increases")

    # Test 4: cordon sanitaire zeroes out excluded player
    def kappa_cordon(S):
        if 'A' in S and len(S) > 1:
            return 0.0
        return kappa(S)

    phi_c = cohesion_shapley(players, weights, threshold, kappa_cordon, 1.0)
    # A can only be pivotal in {A,B} or {A,C} or {A,B,C},
    # all of which have kappa=0, so A gets zero power
    assert phi_c['A'] < 1e-12, f"Cordoned player should have zero power: {phi_c['A']}"
    print("PASS  cordon sanitaire assigns zero power to excluded player")

    # Print sample results
    print("\nApex game indices at selected b values:")
    print(f"  {'b':>5}  {'A':>8}  {'B':>8}  {'C':>8}  {'sum':>8}")
    for b in [0.001, 0.5, 1.0, 2.0, 4.0]:
        phi = cohesion_shapley(players, weights, threshold, kappa, b)
        print(f"  {b:5.3f}  {phi['A']:8.4f}  {phi['B']:8.4f}  {phi['C']:8.4f}"
              f"  {sum(phi.values()):8.4f}")
