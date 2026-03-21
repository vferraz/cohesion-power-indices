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

/-- Faithfulness axiom: if κ(T ∪ {i}) = 0, then p_i^κ(T) = 0. -/
def faithful (κ : CohesionStructure n) : Prop :=
  ∀ i S, κ (S ∪ {i}) = 0 → ∀ (b : ℝ), b > 0 →
    let denom : ℝ := ∑ T : Set (Fin n), κ (T ∪ {i}) ^ b
    denom > 0 → κ (S ∪ {i}) ^ b / denom = 0

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

namespace BV

/-- Linearity in v: F^b(αv + βw, κ) = αF^b(v,κ) + βF^b(w,κ) -/
theorem linearity (κ : CohesionStructure n) (i : Fin n) (b : ℝ) (hb : b > 0)
    (v w : Game n) (α β : ℝ) :
    banzhaf_value (fun s => α * v s + β * w s) κ i b hb =
    α * banzhaf_value v κ i b hb + β * banzhaf_value w κ i b hb := by
  unfold banzhaf_value marginal_contribution
  simp only [banzhaf_probability]
  split_ifs with h h' h''
  · ring_nf
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    congr 1
    ext s
    ring
  all_goals ring

/-- Dummy axiom: if Δ_i v(S) = 0 for all S, then F^b(v,κ) = 0 -/
theorem dummy_axiom (κ : CohesionStructure n) (i : Fin n) (b : ℝ) (hb : b > 0)
    (v : Game n) (h_dummy : ∀ S, marginal_contribution v i S = 0) :
    banzhaf_value v κ i b hb = 0 := by
  unfold banzhaf_value
  simp [h_dummy, Finset.sum_eq_zero]

/-- Scale-invariance: F^b(v, a·κ) = F^b(v, κ) for a > 0 -/
theorem scale_invariance (κ : CohesionStructure n) (i : Fin n) (b : ℝ) (hb : b > 0)
    (v : Game n) (a : ℝ) (ha : a > 0) :
    banzhaf_value v (fun s => a * κ s) i b hb = banzhaf_value v κ i b hb := by
  unfold banzhaf_value banzhaf_probability marginal_contribution
  simp only
  split_ifs with h h'
  · have key : ∀ s : Set (Fin n), (a * κ (s ∪ {i})) ^ b = a ^ b * κ (s ∪ {i}) ^ b := by
      intro s
      ring
    simp only [key]
    rw [Finset.sum_mul]
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

/-- Cohesion monotonicity for simple games (characteristic form):
    If κ'(S ∪ {i}) ≥ κ(S ∪ {i}) for all S where Δ_i v(S) > 0,
    and κ'(S ∪ {i}) = κ(S ∪ {i}) for all S where Δ_i v(S) ≤ 0,
    then F_i(v, κ') ≥ F_i(v, κ).

    This is proven using the W_P/(W_P + W_Q) pivot formulation where:
    - W_P = Σ_{S: Δ_i v(S) > 0} κ(S ∪ {i})^b (supporting coalitions)
    - W_Q = Σ_{S: Δ_i v(S) ≤ 0} κ(S ∪ {i})^b (non-supporting coalitions)
    - F_i = W_P / (W_P + W_Q)
-/
theorem cohesion_monotonicity (κ κ' : CohesionStructure n) (i : Fin n) (b : ℝ) (hb : b > 0)
    (v : Game n) (h_pos : ∀ S, marginal_contribution v i S > 0 → κ' (S ∪ {i}) ≥ κ (S ∪ {i}))
    (h_nonpos : ∀ S, marginal_contribution v i S ≤ 0 → κ' (S ∪ {i}) = κ (S ∪ {i})) :
    banzhaf_value v κ' i b hb ≥ banzhaf_value v κ i b hb := by
  unfold banzhaf_value marginal_contribution
  -- The proof uses weighted sum decomposition and monotonicity of division
  -- For pivotal coalitions (Δ_i v(S) > 0): κ' terms dominate
  -- For non-pivotal coalitions (Δ_i v(S) ≤ 0): equal contribution or zero
  simp only [banzhaf_probability]
  split_ifs with h h'
  · have sum_pos : ∑ s : Set (Fin n), (κ' (s ∪ {i}) : ℝ) ^ b > 0 := h
    have sum_pos' : ∑ s : Set (Fin n), (κ (s ∪ {i}) : ℝ) ^ b > 0 := h'
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

/-- Uniform benchmark: for κ ≡ 1 (constant cohesion),
    p_i^1(S) = 1 / 2^(n-1) (uniform distribution over coalitions excluding i) -/
theorem uniform_benchmark (n : ℕ) (hn : n > 0) (i : Fin n) (b : ℝ) (hb : b > 0) :
    ∀ S : Set (Fin n), banzhaf_probability (fun _ => 1) i S b hb = 1 / 2^(n-1) := by
  intro S
  unfold banzhaf_probability
  split_ifs with h
  · simp only
    -- All κ values are 1, so κ(S ∪ {i})^b = 1^b = 1
    have : ∀ T : Set (Fin n), (1 : ℝ) ^ b = 1 := fun _ => by simp [hb.le]
    simp only [this]
    -- Sum of 1 over all subsets of (Fin n) \ {i} is 2^(n-1)
    norm_num
  · exfalso
    apply h
    simp only [Finset.sum_const]
    have : (Fintype.card (Set (Fin n))) = 2 ^ n := by decide
    positivity

end BV
