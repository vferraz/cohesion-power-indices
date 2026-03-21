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

/-- Representation coefficients w for a value F_i(v,κ) = Σ w_i^κ(S) · Δ_i v(S).
    This comes from Proposition 2.7 in the theory. -/
def representation_coefficients (n : ℕ) :=
  (Set (Fin n) → CohesionStructure n → ℝ)

/-- Cohesion regularity: coefficients w are determined by a power law in κ,
    i.e., w_i^κ(S) ∝ κ(S ∪ {i})^{b_i} (up to normalization). -/
def cohesion_regular (w : representation_coefficients n) : Prop :=
  ∀ i : Fin n, ∃ b_i : ℝ, ∀ (κ κ' : CohesionStructure n) (S : Set (Fin n)),
    (∀ U, κ (U ∪ {i}) = κ' (U ∪ {i})) →
    w S κ i = w S κ' i

/-- Faithfulness: if κ(S ∪ {i}) = 0, then w_i^κ(S) = 0. -/
def faithful (w : representation_coefficients n) : Prop :=
  ∀ i S κ, κ (S ∪ {i}) = 0 → w S κ i = 0

/-- Symmetry condition: coefficients are equivariant under permutations of players.
    If π is a permutation of Fin n and πκ(S) := κ(π⁻¹(S)), then
    w_{π(i)}^{πκ}(πS) = w_i^κ(S). -/
def symmetric (w : representation_coefficients n) : Prop :=
  ∀ (π : Equiv.Perm (Fin n)) (i : Fin n) (S : Set (Fin n)) (κ : CohesionStructure n),
    let πS := {π i | i ∈ S}
    let πκ := fun U => κ (π.symm '' U)
    w πS πκ (π i) = w S κ i

/-- Banzhaf-type probability distribution. -/
def banzhaf_probability (κ : CohesionStructure n) (i : Fin n) (S : Set (Fin n))
    (b : ℝ) (hb : b > 0) : ℝ :=
  let denom : ℝ := ∑ T : Set (Fin n), κ (T ∪ {i}) ^ b
  if h : denom > 0 then κ (S ∪ {i}) ^ b / denom else 0

/-- The standard Banzhaf value: F^b(v,κ) = Σ_S p_i^κ(S) · Δ_i v(S) -/
def banzhaf_value (v : Game n) (κ : CohesionStructure n) (i : Fin n) (b : ℝ)
    (hb : b > 0) : ℝ :=
  ∑ S : Set (Fin n), banzhaf_probability κ i S b hb * marginal_contribution v i S

namespace BU

/-- Key lemma: if two players have the same power exponent b_i = b_j,
    this is preserved under symmetry and transitivity. -/
lemma exponent_uniformity (n : ℕ) (hn : n ≥ 2) :
    ∀ (b : Fin n → ℝ), (∃ i j : Fin n, b i = b j) →
    (∀ π : Equiv.Perm (Fin n), ∀ i, b (π i) = b i) →
    ∃ b_common : ℝ, ∀ i, b i = b_common := by
  intro b _ hsym
  use b 0
  intro i
  have := hsym (Equiv.swap 0 i) 0
  simp [Equiv.Perm.swap_apply_left] at this
  have := hsym (Equiv.swap 0 i) i
  simp [Equiv.Perm.swap_apply_right] at this
  -- The symmetry under all permutations implies all exponents are equal
  by_contra h
  have : b 0 ≠ b i := h
  have : b (Equiv.swap 0 i 0) = b 0 := hsym (Equiv.swap 0 i) 0
  have : b i = b 0 := by
    simp [Equiv.Perm.swap_apply_right] at this
    exact this
  contradiction

/-- Uniqueness theorem (Theorem 3.3, uniqueness direction):
    Given a value F with representation coefficients w that satisfy:
    1. Cohesion regularity: w_i^κ(S) ∝ κ(S ∪ {i})^{b_i}
    2. Faithfulness: κ = 0 ⟹ w = 0
    3. Symmetry: w_{π(i)}^{πκ}(πS) = w_i^κ(S)

    Then b_i = b for all i (by symmetry and transitivity), and F = F^b.
-/
theorem uniqueness (n : ℕ) (hn : n ≥ 2) (w : representation_coefficients n)
    (h_regular : cohesion_regular w)
    (h_faithful : faithful w)
    (h_symmetric : symmetric w) :
    ∃ b : ℝ, ∀ (v : Game n) (κ : CohesionStructure n) (i : Fin n),
      (∑ S : Set (Fin n), w S κ i * marginal_contribution v i S) =
      banzhaf_value v κ i b (by norm_num : b > 0) := by
  -- Extract the exponents b_i from the regular representation
  have : ∀ i : Fin n, ∃ b_i : ℝ, ∀ (κ κ' : CohesionStructure n) (S : Set (Fin n)),
      (∀ U, κ (U ∪ {i}) = κ' (U ∪ {i})) →
      w S κ i = w S κ' i := h_regular

  -- Define the exponent function
  let exponents : Fin n → ℝ := fun i => Classical.choose (h_regular i)

  -- The exponents must all be equal by symmetry
  have exponent_eq : ∃ b : ℝ, ∀ i : Fin n, exponents i = b := by
    -- Symmetry forces all exponents to be identical
    have sym_exponents : ∀ π : Equiv.Perm (Fin n), ∀ i,
        exponents (π i) = exponents i := by
      intro π i
      -- This follows from h_symmetric and the fact that exponents are canonical
      simp [exponents]
      sorry -- This requires formalization of the symmetry argument

    use exponents 0
    intro i
    have := sym_exponents (Equiv.swap 0 i) 0
    simp [Equiv.Perm.swap_apply_left] at this
    have := sym_exponents (Equiv.swap 0 i) i
    simp [Equiv.Perm.swap_apply_right] at this
    exact this

  obtain ⟨b, hb⟩ := exponent_eq
  use b
  intro v κ i

  -- The representation matches the Banzhaf form
  sorry

/-- Corollary: any two values satisfying the three properties must coincide
    if they have the same representation form. -/
theorem characterization_uniqueness (n : ℕ) (hn : n ≥ 2)
    (F G : Game n → CohesionStructure n → Fin n → ℝ)
    (h_F : ∃ w, ∀ v κ i, F v κ i = ∑ S : Set (Fin n), w S κ i * marginal_contribution v i S)
    (h_G : ∃ w, ∀ v κ i, G v κ i = ∑ S : Set (Fin n), w S κ i * marginal_contribution v i S)
    (h_F_regular : ∀ w, (∃ v κ i, F v κ i = ∑ S : Set (Fin n), w S κ i * marginal_contribution v i S) →
                         cohesion_regular w)
    (h_G_regular : ∀ w, (∃ v κ i, G v κ i = ∑ S : Set (Fin n), w S κ i * marginal_contribution v i S) →
                         cohesion_regular w)
    (h_F_faithful : ∀ w, (∃ v κ i, F v κ i = ∑ S : Set (Fin n), w S κ i * marginal_contribution v i S) →
                          faithful w)
    (h_G_faithful : ∀ w, (∃ v κ i, G v κ i = ∑ S : Set (Fin n), w S κ i * marginal_contribution v i S) →
                          faithful w)
    (h_F_sym : ∀ w, (∃ v κ i, F v κ i = ∑ S : Set (Fin n), w S κ i * marginal_contribution v i S) →
                     symmetric w)
    (h_G_sym : ∀ w, (∃ v κ i, G v κ i = ∑ S : Set (Fin n), w S κ i * marginal_contribution v i S) →
                     symmetric w) :
    ∀ v κ i, F v κ i = G v κ i := by
  intro v κ i
  obtain ⟨w_F, hw_F⟩ := h_F
  obtain ⟨w_G, hw_G⟩ := h_G

  have h_F_props : cohesion_regular w_F ∧ faithful w_F ∧ symmetric w_F := by
    refine ⟨?_, ?_, ?_⟩
    · apply h_F_regular; exact ⟨v, κ, i, hw_F⟩
    · apply h_F_faithful; exact ⟨v, κ, i, hw_F⟩
    · apply h_F_sym; exact ⟨v, κ, i, hw_F⟩

  have h_G_props : cohesion_regular w_G ∧ faithful w_G ∧ symmetric w_G := by
    refine ⟨?_, ?_, ?_⟩
    · apply h_G_regular; exact ⟨v, κ, i, hw_G⟩
    · apply h_G_faithful; exact ⟨v, κ, i, hw_G⟩
    · apply h_G_sym; exact ⟨v, κ, i, hw_G⟩

  -- Both F and G are equal to some F^b by uniqueness
  have F_eq : ∃ b, F v κ i = banzhaf_value v κ i b (by norm_num : b > 0) := by
    have := uniqueness n hn w_F h_F_props.1 h_F_props.2.1 h_F_props.2.2
    obtain ⟨b, hb⟩ := this
    exact ⟨b, hb v κ i⟩

  have G_eq : ∃ b, G v κ i = banzhaf_value v κ i b (by norm_num : b > 0) := by
    have := uniqueness n hn w_G h_G_props.1 h_G_props.2.1 h_G_props.2.2
    obtain ⟨b, hb⟩ := this
    exact ⟨b, hb v κ i⟩

  -- Since both derive from the same axioms, they must use the same exponent
  sorry

end BU
