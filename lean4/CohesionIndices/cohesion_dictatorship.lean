import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- A game v : P(N) → ℝ assigns payoffs to coalitions. -/
def Game (n : ℕ) := Set (Fin n) → ℝ

/-- A cohesion structure κ : P(N) → ℝ_≥0 assigns cohesion weights to coalitions. -/
def CohesionStructure (n : ℕ) := Set (Fin n) → ℝ

/-- Marginal contribution: Δ_i v(S) = v(S ∪ {i}) - v(S) -/
def marginal_contribution (v : Game n) (i : Fin n) (S : Set (Fin n)) : ℝ :=
  v (S ∪ {i}) - v S

/-- A dictator game with dictator d: v(S) = 1 if d ∈ S, 0 otherwise. -/
def dictator_game (n : ℕ) (d : Fin n) : Game n :=
  fun S => if d ∈ S then 1 else 0

/-- Banzhaf-type probability distribution for player i:
    p_i^κ(S) = κ(S ∪ {i})^b / Σ_T κ(T ∪ {i})^b -/
def banzhaf_probability (κ : CohesionStructure n) (i : Fin n) (S : Set (Fin n))
    (b : ℝ) (hb : b > 0) : ℝ :=
  let denom : ℝ := ∑ T : Set (Fin n), κ (T ∪ {i}) ^ b
  if h : denom > 0 then κ (S ∪ {i}) ^ b / denom else 0

/-- Banzhaf-type power index: F^b(v,κ) = Σ_S p_i^κ(S) · Δ_i v(S) -/
def banzhaf_value (v : Game n) (κ : CohesionStructure n) (i : Fin n) (b : ℝ)
    (hb : b > 0) : ℝ :=
  ∑ S : Set (Fin n), banzhaf_probability κ i S b hb * marginal_contribution v i S

/-- Shapley-type probability with size weights. -/
def shapley_probability (α : Fin n → ℝ) (κ : CohesionStructure n) (i : Fin n)
    (S : Set (Fin n)) (b : ℝ) (hb : b > 0) : ℝ :=
  let size := (S.ncard : ℝ)
  let weight := if h : size < n then α ⟨(S.ncard : ℕ), by omega⟩ else 1
  let numerator := weight * κ (S ∪ {i}) ^ b
  let denom : ℝ := ∑ T : Set (Fin n),
    let sz := (T.ncard : ℝ)
    let w := if h : sz < n then α ⟨(T.ncard : ℕ), by omega⟩ else 1
    w * κ (T ∪ {i}) ^ b
  if h : denom > 0 then numerator / denom else 0

/-- Shapley-type power index with size weights. -/
def shapley_value (α : Fin n → ℝ) (v : Game n) (κ : CohesionStructure n) (i : Fin n)
    (b : ℝ) (hb : b > 0) : ℝ :=
  ∑ S : Set (Fin n), shapley_probability α κ i S b hb * marginal_contribution v i S

namespace DI

/-- Helper: p is a probability distribution (sums to 1). -/
lemma probability_sum (p : Set (Fin n) → ℝ) (hp : ∀ S, 0 ≤ p S)
    (hp_sum : ∑ S : Set (Fin n), p S = 1) (S : Set (Fin n)) :
    0 ≤ p S ∧ p S ≤ 1 := by
  constructor
  · exact hp S
  · have : ∑ T : Set (Fin n), p T = 1 := hp_sum
    have : p S ≤ ∑ T : Set (Fin n), p T := by
      gcongr
      apply Finset.sum_le_sum
      intro T _
      split_ifs
      · exact hp T
      · exact hp T
    linarith

/-- Banzhaf probabilities form a probability distribution:
    Σ_S p_i^κ(S) · 1 = 1 (given positive cohesion). -/
lemma banzhaf_prob_sum (κ : CohesionStructure n) (i : Fin n) (b : ℝ) (hb : b > 0)
    (h_pos : ∃ S, κ (S ∪ {i}) > 0) :
    ∑ S : Set (Fin n), banzhaf_probability κ i S b hb = 1 := by
  unfold banzhaf_probability
  split_ifs with h
  · field_simp [h]
    ring
  · exfalso
    apply h
    obtain ⟨S, hS⟩ := h_pos
    have : κ (S ∪ {i}) ^ b > 0 := by positivity
    have : ∑ T : Set (Fin n), κ (T ∪ {i}) ^ b ≥ κ (S ∪ {i}) ^ b := by
      gcongr
      apply Finset.sum_le_sum
      intro T _
      positivity
    linarith

/-- Shapley probabilities form a probability distribution. -/
lemma shapley_prob_sum (α : Fin n → ℝ) (κ : CohesionStructure n) (i : Fin n)
    (b : ℝ) (hb : b > 0) (h_pos : ∃ S, κ (S ∪ {i}) > 0) :
    ∑ S : Set (Fin n), shapley_probability α κ i S b hb = 1 := by
  unfold shapley_probability
  split_ifs with h
  · field_simp [h]
    ring
  · exfalso
    apply h
    obtain ⟨S, hS⟩ := h_pos
    have : κ (S ∪ {i}) ^ b > 0 := by positivity
    have : ∑ T : Set (Fin n),
      (let sz := (T.ncard : ℝ)
       let w := if h : sz < n then α ⟨(T.ncard : ℕ), by omega⟩ else 1
       w * κ (T ∪ {i}) ^ b) ≥
      (let sz := (S.ncard : ℝ)
       let w := if h : sz < n then α ⟨(S.ncard : ℕ), by omega⟩ else 1
       w * κ (S ∪ {i}) ^ b) := by
      gcongr
      apply Finset.sum_le_sum
      intro T _
      positivity
    linarith

/-- In a dictator game v with dictator d, the marginal contribution of player j ≠ d is zero. -/
lemma dictator_marginal_nondict (n : ℕ) (d j : Fin n) (S : Set (Fin n))
    (h_ne : j ≠ d) :
    marginal_contribution (dictator_game n d) j S = 0 := by
  unfold dictator_game marginal_contribution
  simp only
  split_ifs with h h'
  · -- Both j and d in S ∪ {j}, and in S ∪ {j}: d ∈ S ∪ {j} iff d ∈ S or j = d
    have : d ∈ S ∪ {j} ↔ d ∈ S ∨ d = j := by
      simp [Set.mem_union, Set.mem_singleton_iff]
    simp [this] at h'
    cases h' with
    | inl hd => exact absurd hd h
    | inr heq => exact absurd heq h_ne
  · -- d ∈ S
    have : d ∈ S ∪ {j} := Set.mem_union_left _ h
    contradiction
  · ring

/-- In a dictator game v with dictator d, the marginal contribution of d is always 1. -/
lemma dictator_marginal_dict (n : ℕ) (d : Fin n) (S : Set (Fin n)) (hnd : d ∉ S) :
    marginal_contribution (dictator_game n d) d S = 1 := by
  unfold dictator_game marginal_contribution
  simp only
  have : d ∈ S ∪ {d} := Set.mem_union_right _ (Set.mem_singleton d)
  simp [this, hnd]

/-- Dictatorship invariance for Banzhaf: non-dictator receives zero power. -/
theorem banzhaf_dictator_zero (n : ℕ) (d j : Fin n) (κ : CohesionStructure n)
    (b : ℝ) (hb : b > 0) (h_ne : j ≠ d) (h_pos : ∃ S, κ (S ∪ {j}) > 0) :
    banzhaf_value (dictator_game n d) κ j b hb = 0 := by
  unfold banzhaf_value
  apply Finset.sum_eq_zero
  intro S _
  have : marginal_contribution (dictator_game n d) j S = 0 := dictator_marginal_nondict n d j S h_ne
  simp [this]

/-- Dictatorship invariance for Banzhaf: dictator receives total power.
    This requires that d is not in any coalition S (since marginal is from S to S∪{d}),
    and integrating the probability distribution. -/
theorem banzhaf_dictator_one (n : ℕ) (d : Fin n) (κ : CohesionStructure n)
    (b : ℝ) (hb : b > 0) (h_pos : ∃ S, κ (S ∪ {d}) > 0) :
    banzhaf_value (dictator_game n d) κ d b hb = 1 := by
  unfold banzhaf_value
  have prob_sum : ∑ S : Set (Fin n), banzhaf_probability κ d S b hb = 1 :=
    banzhaf_prob_sum κ d b hb h_pos

  have key : ∀ S : Set (Fin n), d ∉ S → marginal_contribution (dictator_game n d) d S = 1 :=
    fun S _ => dictator_marginal_dict n d S (by trivial)

  have key' : ∀ S : Set (Fin n), d ∈ S → marginal_contribution (dictator_game n d) d S = 0 := by
    intro S hd
    unfold dictator_game marginal_contribution
    simp [hd]

  calc ∑ S : Set (Fin n), banzhaf_probability κ d S b hb * marginal_contribution (dictator_game n d) d S
    = ∑ S : Set (Fin n) | d ∉ S, banzhaf_probability κ d S b hb * 1 +
      ∑ S : Set (Fin n) | d ∈ S, banzhaf_probability κ d S b hb * 0 := by
      rw [Finset.sum_subset]
      · intro S _
        split_ifs with h
        · exact key' S h
        · exact key S h
      · intro _ _; simp
    _ = ∑ S : Set (Fin n) | d ∉ S, banzhaf_probability κ d S b hb := by
      simp [zero_mul, Finset.sum_eq_zero_iff]
    _ = ∑ S : Set (Fin n), banzhaf_probability κ d S b hb := by
      rw [Finset.sum_subset]
      · intro S _; simp
      · intro _ _; simp
    _ = 1 := prob_sum

/-- Dictatorship invariance for Shapley: non-dictator receives zero power. -/
theorem shapley_dictator_zero (n : ℕ) (d j : Fin n) (α : Fin n → ℝ) (κ : CohesionStructure n)
    (b : ℝ) (hb : b > 0) (h_ne : j ≠ d) (h_pos : ∃ S, κ (S ∪ {j}) > 0) :
    shapley_value α (dictator_game n d) κ j b hb = 0 := by
  unfold shapley_value
  apply Finset.sum_eq_zero
  intro S _
  have : marginal_contribution (dictator_game n d) j S = 0 := dictator_marginal_nondict n d j S h_ne
  simp [this]

/-- Dictatorship invariance for Shapley: dictator receives total power. -/
theorem shapley_dictator_one (n : ℕ) (d : Fin n) (α : Fin n → ℝ) (κ : CohesionStructure n)
    (b : ℝ) (hb : b > 0) (h_pos : ∃ S, κ (S ∪ {d}) > 0) :
    shapley_value α (dictator_game n d) κ d b hb = 1 := by
  unfold shapley_value
  have prob_sum : ∑ S : Set (Fin n), shapley_probability α κ d S b hb = 1 :=
    shapley_prob_sum α κ d b hb h_pos

  have key : ∀ S : Set (Fin n), d ∉ S → marginal_contribution (dictator_game n d) d S = 1 :=
    fun S _ => dictator_marginal_dict n d S (by trivial)

  have key' : ∀ S : Set (Fin n), d ∈ S → marginal_contribution (dictator_game n d) d S = 0 := by
    intro S hd
    unfold dictator_game marginal_contribution
    simp [hd]

  calc ∑ S : Set (Fin n), shapley_probability α κ d S b hb * marginal_contribution (dictator_game n d) d S
    = ∑ S : Set (Fin n) | d ∉ S, shapley_probability α κ d S b hb * 1 +
      ∑ S : Set (Fin n) | d ∈ S, shapley_probability α κ d S b hb * 0 := by
      rw [Finset.sum_subset]
      · intro S _
        split_ifs with h
        · exact key' S h
        · exact key S h
      · intro _ _; simp
    _ = ∑ S : Set (Fin n) | d ∉ S, shapley_probability α κ d S b hb := by
      simp [zero_mul, Finset.sum_eq_zero_iff]
    _ = ∑ S : Set (Fin n), shapley_probability α κ d S b hb := by
      rw [Finset.sum_subset]
      · intro S _; simp
      · intro _ _; simp
    _ = 1 := prob_sum

end DI
