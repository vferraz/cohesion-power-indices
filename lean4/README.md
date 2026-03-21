# Lean 4 Formal Verification

Machine-verified proofs for all characterization theorems and supporting lemmas in
"Cohesion-Sensitive Power Indices: Representation Results for Banzhaf and Shapley Values"
(Pitz & Ferraz, 2026).

**Toolchain:** Lean 4 v4.24.0, Mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`
**Verification engine:** [Aristotle](https://aristotle.harmonic.fun) (Harmonic)

## Building

```bash
cd lean4
lake build
```

This will download Mathlib (may take several minutes on first run) and type-check all
source files.

## Directory structure

- `CohesionIndices/` — Human-authored Lean input files (problem specifications)
- `Aristotle/` — Machine-generated proofs returned by Aristotle

## File-to-paper mapping

### Input files (CohesionIndices/)

| File | Paper results covered |
|------|----------------------|
| `cohesion_banzhaf_verification.lean` | Lemma 2.5 (marginal dichotomy), Lemma A.1 (Luce representation), Lemma 2.8/2.9 (Banzhaf axiom verification) |
| `cohesion_banzhaf_uniqueness.lean` | Proposition 2.7 (probabilistic representation), Theorem 3.1 (Banzhaf characterization), Lemma A.2 (size-cohesion separability) |
| `cohesion_shapley_verification.lean` | Theorem 3.3 (Shapley characterization), Lemma 2.10/2.11 (Shapley axiom verification) |
| `cohesion_dictatorship.lean` | Lemma 2.6 (dictatorship invariance under cohesion) |

### Aristotle output files (Aristotle/)

| File (UUID) | What is proved |
|-------------|----------------|
| `eabe0391-...` | `PBr.marginal_zero_or_one_of_monotone` — marginal contributions in monotone simple games are in {0,1} |
| `db334b2f-...` | `P3a.probabilistic_representation` — any linear, dummy-respecting value admits a probability representation |
| `e0bd247a-...` | `P3d.banzhaf_assembly`, `P3d.shapley_assembly` — assembly of Banzhaf/Shapley characterizations |
| `d9cc39a7-...` | `P3b.luce_representation_corrected` — Luce-type representation (with faithfulness correction) + counterexample |
| `6fcd6550-...` | `P3c.size_kappa_multiplicative` — size-cohesion separability under symmetry |
| `06338b25-...` | `P2a.verification_banzhaf_scaleInvariance`, `P2a.verification_shapley_scaleInvariance` |
| `d0130781-...` | `P2b.verification_banzhaf_uniform`, `P2b.verification_shapley_benchmark` — uniform/size-weight benchmark |
| `6ec7c99d-...` | `P2d.verification_banzhaf_cohesionMono`, `P2d.verification_shapley_cohesionMono` |
| `7d66836b-...` | `P2c.dictator_banzhaf_value_one`, `P2c.dictator_shapley_value_one` — dictatorship invariance |

## Notable finding

During formal verification, Aristotle discovered that the original statement of Lemma A.1
(Luce representation) was **false as stated**. The proof requires a faithfulness assumption
(zero cohesion implies zero probability) not present in the initial formulation. The file
`d9cc39a7-...-output.lean` contains both the corrected theorem
(`P3b.luce_representation_corrected`) and a formal counterexample
(`P3b.counterexample_to_luce_proof`) demonstrating the original is unprovable.
