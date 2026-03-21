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

/-- Size weights α : {0,...,n-1} → ℝ_> 0 provide different emphasis based on coalition size. -/
def SizeWeights (n : ℕ) := Fin n → ℝ

/-- Marginal contribution: Δ_i v(S) = v(S ∪ {i}) - v(S) -/
def marginal_contribution (v : Game n) (i : Fin n) (S : Set (Fin n)) : ℝ :=
  v (S ∪ {i}) - v S

/-- Shapley-type probability distribution with size weights and cohesion:
    p_i^κ(S) = α_{|S|} · κ(S ∪ {i})^b / Σ_T α_{|T|} · κ(T ∪ {i})^b -/
def shapley_probability (α : SizeWeights n) (κ : CohesionStructure n) (i : Fin n)
    (S : Set (Fin n)) (b : ℝ) (hb : b > 0) : ℝ :=
  let size := (S.ncard : ℝ)
  let weight := if h : size < n then α ⟨(S.ncard : ℕ), by omega⟩ else 1
  let numerator := weight * κ (S ∪ {i}) ^ b
  let denom : ℝ := ∑ T : Set (Fin n),
    let sz := (T.ncard : ℝ)
    let w := if h : sz < n then α ⟨(T.ncard : ℕ), by omega⟩ else 1
    w * κ (T ∪ {i}) ^ b
  if h : denom > 0 then numerator / denom else 0

/-- Shapley-type power index with size weights:
    F_i(v, κ, α, b) = Σ_S p_i^κ(S) · Δ_i v(S) -/
def shapley_value (α : SizeWeights n) (v : Game n) (κ : CohesionStructure n) (i : Fin n)
    (b : ℝ) (hb : b > 0) : ℝ :=
  ∑ S : Set (Fin n), shapley_probability α κ i S b hb * marginal_contribution v i S

namespace SV

/-- Linearity in v: F(αv + βw, κ, α, b) = αF(v, κ, α, b) + βF(w, κ, α, b) -/
theorem linearity (α : SizeWeights n) (κ : CohesionStructure n) (i : Fin n) (b : ℝ) (hb : b > 0)
    (v w : Game n) (c d : ℝ) :
    shapley_value α (fun s => c * v s + d * w s) κ i b hb =
    c * shapley_value α v κ i b hb + d * shapley_value α w κ i b hb := by
  unfold shapley_value marginal_contribution shapley_probability
  simp only
  split_ifs with _ _ _ _
  · ring_nf
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    congr 1
    ext s
    ring
  all_goals ring

/-- Dummy axiom: if Δ_i v(S) = 0 for all S, then F(v, κ, α, b) = 0 -/
theorem dummy_axiom (α : SizeWeights n) (κ : CohesionStructure n) (i : Fin n) (b : ℝ) (hb : b > 0)
    (v : Game n) (h_dummy : ∀ S, marginal_contribution v i S = 0) :
    shapley_value α v κ i b hb = 0 := by
  unfold shapley_value
  simp [h_dummy, Finset.sum_eq_zero]

/-- Scale-invariance: F(v, a·κ, α, b) = F(v, κ, α, b) for a > 0 -/
theorem scale_invariance (α : SizeWeights n) (κ : CohesionStructure n) (i : Fin n) (b : ℝ)
    (hb : b > 0) (v : Game n) (a : ℝ) (ha : a > 0) :
    shapley_value α v (fun s => a * κ s) i b hb = shapley_value α v κ i b hb := by
  unfold shapley_value shapley_probability marginal_contribution
  simp only
  split_ifs with h h'
  · have key : ∀ s : Set (Fin n), (a * κ (s ∪ {i})) ^ b = a ^ b * κ (s ∪ {i}) ^ b := by
      intro s; ring
    simp only [key]
    rw [← Finset.sum_mul]
    congr 1
    ext s
    field_simp
    ring
  all_goals
    have : ∀ s : Set (Fin n), (a * κ (s ∪ {i})) ^ b = a ^ b * κ (s ∪ {i}) ^ b := by
      intro s; ring
    simp only [this] at h
    have : 0 < a ^ b := by positivity
    linarith

/-- Cohesion monotonicity for simple games with size weights:
    Uses the same W_P/(W_P + W_Q) argument but weighted by α_{|S|}.
    If κ'(S ∪ {i}) ≥ κ(S ∪ {i}) for pivotal S and equality otherwise,
    then F_i(v, κ', α, b) ≥ F_i(v, κ, α, b).
-/
theorem cohesion_monotonicity (α : SizeWeights n) (κ κ' : CohesionStructure n) (i : Fin n)
    (b : ℝ) (hb : b > 0) (v : Game n)
    (h_pos : ∀ S, marginal_contribution v i S > 0 → κ' (S ∪ {i}) ≥ κ (S ∪ {i}))
    (h_nonpos : ∀ S, marginal_contribution v i S ≤ 0 → κ' (S ∪ {i}) = κ (S ∪ {i})) :
    shapley_value α v κ' i b hb ≥ shapley_value α v κ i b hb := by
  unfold shapley_value marginal_contribution shapley_probability
  simp only
  split_ifs with h h'
  · have sum_pos : ∑ s : Set (Fin n),
      (let sz := (s.ncard : ℝ)
       let w := if h : sz < n then α ⟨(s.ncard : ℕ), by omega⟩ else 1
       w * (κ' (s ∪ {i}) : ℝ) ^ b) > 0 := h
    have sum_pos' : ∑ s : Set (Fin n),
      (let sz := (s.ncard : ℝ)
       let w := if h : sz < n then α ⟨(s.ncard : ℕ), by omega⟩ else 1
       w * (κ (s ∪ {i}) : ℝ) ^ b) > 0 := h'
    gcongr
    apply Finset.sum_le_sum
    intro S _
    split_ifs with hp
    · have : κ' (S ∪ {i}) ≥ κ (S ∪ {i}) := h_pos S hp
      gcongr
    · by_cases hnp : marginal_contribution v i S ≤ 0
      · have : κ' (S ∪ {i}) = κ (S ∪ {i}) := h_nonpos S hnp
        simp [this]
      · push_neg at hnp
        simp [hnp] at hp
  all_goals
    (try { have : False := by linarith }) <|> rfl

/-- Size-cohesion separability (by construction):
    p_i^κ(S) factors as p_i^κ(S) = (α_{|S|} · κ(S ∪ {i})^b) / (Σ_T α_{|T|} · κ(T ∪ {i})^b),
    making size weight and cohesion contributions independent. -/
theorem size_cohesion_separability (α : SizeWeights n) (κ : CohesionStructure n) (i : Fin n)
    (S : Set (Fin n)) (b : ℝ) (hb : b > 0) :
    ∃ (f : ℕ → ℝ) (g : Set (Fin n) → ℝ),
      shapley_probability α κ i S b hb = f (S.ncard) * g (S ∪ {i}) := by
  use fun k => (if h : (k : ℝ) < n then α ⟨k, by omega⟩ else 1) /
    (∑ T : Set (Fin n),
      (let sz := (T.ncard : ℝ)
       let w := if h : sz < n then α ⟨(T.ncard : ℕ), by omega⟩ else 1
       w * κ (T ∪ {i}) ^ b))
  use fun U => κ U ^ b
  unfold shapley_probability
  split_ifs <|> rfl
  ring

/-- Cohesionless benchmark: for κ ≡ 1 (constant cohesion),
    p_i^1(S) = α_{|S|} / Σ_k α_k (only depends on coalition size).
-/
theorem cohesionless_benchmark (α : SizeWeights n) (i : Fin n) (S : Set (Fin n)) (b : ℝ) (hb : b > 0) :
    shapley_probability α (fun _ => 1) i S b hb =
    (if h : (S.ncard : ℝ) < n then α ⟨S.ncard, by omega⟩ else 1) /
    (∑ k : Fin n, if h : (k : ℝ) < n then α ⟨k.val, by omega⟩ else 1) := by
  unfold shapley_probability
  split_ifs with h h'
  · simp only
    -- All κ values are 1, so κ(S ∪ {i})^b = 1^b = 1
    have : ∀ T : Set (Fin n), (1 : ℝ) ^ b = 1 := fun _ => by simp [hb.le]
    simp only [this, mul_one]
    congr 1
    ext k
    simp [Fin.sum_univ_succ]
  all_goals simp at h h'

end SV
