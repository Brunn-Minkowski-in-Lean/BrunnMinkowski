import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.RCLike.Basic
import BrunnMinkowski.EuclideanSpace
import Mathlib

open NNReal ENNReal MeasureTheory Finset
open Real Set MeasureTheory Filter Asymptotics

open scoped Real Topology

-- isomorhpism from any f.d. R-v.s. to R^d
#check toEuclidean

class EuclideanIsomorphismInvariant.{u}
    (P : (α : Type u) → [AddCommGroup α] → [TopologicalSpace α] → [TopologicalAddGroup α] →
      [T2Space α] → [Module ℝ α] → [ContinuousSMul ℝ α] → [FiniteDimensional ℝ α] → Prop) :
    Prop where
  isomorphism_invariant
      (α : Type u) [AddCommGroup α] [TopologicalSpace α] [TopologicalAddGroup α] [T2Space α]
        [Module ℝ α] [ContinuousSMul ℝ α] [FiniteDimensional ℝ α]
      (β : Type u) [AddCommGroup β] [TopologicalSpace β] [TopologicalAddGroup β] [T2Space β]
        [Module ℝ β] [ContinuousSMul ℝ β] [FiniteDimensional ℝ β]
      (h : α ≃L[ℝ] β) :
    P α ↔ P β

-- TODO: Remove sorry.
def EuclideanSpace.finProdLinearEquiv (n₁ n₂ : ℕ) :
    ((EuclideanSpace ℝ (Fin n₁)) × (EuclideanSpace ℝ (Fin n₂))) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (n₁ + n₂)) :=
  ⟨sorry, sorry, sorry⟩

-- TODO: Consider higher order types if possible.
theorem EuclideanSpace.induction_on_finrank
    {P : (α : Type) → [AddCommGroup α] → [TopologicalSpace α] → [TopologicalAddGroup α] →
      [T2Space α] → [Module ℝ α] → [ContinuousSMul ℝ α] → [FiniteDimensional ℝ α] → Prop}
    [EuclideanIsomorphismInvariant P]
    {base0 : (α : Type) → [AddCommGroup α] → [TopologicalSpace α] → [TopologicalAddGroup α] →
      [T2Space α] → [Module ℝ α] → [ContinuousSMul ℝ α] → [FiniteDimensional ℝ α] →
      Module.finrank ℝ α = 0 → P α}
    {base1 : (α : Type) → [AddCommGroup α] → [TopologicalSpace α] → [TopologicalAddGroup α] →
      [T2Space α] → [Module ℝ α] → [ContinuousSMul ℝ α] → [FiniteDimensional ℝ α] →
      Module.finrank ℝ α = 1 → P α}
    {induct : {α : Type} → [AddCommGroup α] → [TopologicalSpace α] → [TopologicalAddGroup α] →
      [T2Space α] → [Module ℝ α] → [ContinuousSMul ℝ α] → [FiniteDimensional ℝ α] →
      {β : Type} → [AddCommGroup β] → [TopologicalSpace β] → [TopologicalAddGroup β] →
      [T2Space β] → [Module ℝ β] → [ContinuousSMul ℝ β] → [FiniteDimensional ℝ β] →
      P α → P β → P (α × β)}
    (α : Type) [AddCommGroup α] [TopologicalSpace α] [TopologicalAddGroup α] [T2Space α]
    [Module ℝ α] [ContinuousSMul ℝ α] [FiniteDimensional ℝ α] : P α := by
  induction' h₀ : Module.finrank ℝ α using Nat.strong_induction_on generalizing α
  case h n ih _ _ _ _ _ _ _ =>
    match n with
    | 0 => exact base0 _ h₀
    | 1 => exact base1 _ h₀
    | n + 2 =>
      let eqv : α ≃L[ℝ] (EuclideanSpace ℝ (Fin (n + 1)) × EuclideanSpace ℝ (Fin 1)) :=
        ContinuousLinearEquiv.trans (h₀ ▸ @toEuclidean α _ _ _ _ _ _ _)
          (EuclideanSpace.finProdLinearEquiv (n + 1) 1).symm
      exact (‹EuclideanIsomorphismInvariant P›.isomorphism_invariant α _ eqv).mpr (induct
        (ih (n + 1) (by omega) _ finrank_euclideanSpace_fin)
        (ih 1 (by omega) _ finrank_euclideanSpace_fin))

theorem Nat.induction_on_sum
    {motive : ℕ → Prop}
    (hzero : motive 0)
    (hone : motive 1)
    (ind : ∀ ⦃n₁ : ℕ⦄, motive n₁ → ∀ ⦃n₂ : ℕ⦄, motive n₂ → motive (n₁ + n₂))
    (n : ℕ) :
    motive n := by
  induction n
  case zero => exact hzero
  case succ n ih => match n with
  | 0 => exact hone
  | n + 1 => exact ind ih hone

set_option linter.unusedVariables false in
def condition
    {t : ℝ} (ht₁ : 0 < t) (ht₂ : t < 1) {d : ℕ}
    (f : ℝn d → ℝ) (hf : ∀ x, 0 ≤ f x)
    (g : ℝn d → ℝ) (hg : ∀ x, 0 ≤ g x)
    (h : ℝn d → ℝ) : Prop :=
  ∀ x y : ℝn d, (f x) ^ (1 - t) * (g y) ^ t ≤ h (x + y)

theorem condition_nonneg
    {t : ℝ} (ht₁ : 0 < t) (ht₂ : t < 1) {d : ℕ}
    {f : ℝn d → ℝ} (hf : ∀ x, 0 ≤ f x)
    {g : ℝn d → ℝ} (hg : ∀ x, 0 ≤ g x)
    {h : ℝn d → ℝ} (h₀ : condition ht₁ ht₂ _ hf _ hg h) {x : ℝn d} :
    0 ≤ h x := by
  refine le_trans ?_ (add_zero x ▸ h₀ x 0)
  have := hf x; have := hg 0; positivity

def prekopa_leindler_statement
    {t : ℝ} (ht₁ : 0 < t) (ht₂ : t < 1) {d : ℕ}
    (f : ℝn d → ℝ) (hf : ∀ x, 0 ≤ f x)
    (g : ℝn d → ℝ) (hg : ∀ x, 0 ≤ g x)
    (h : ℝn d → ℝ) : Prop :=
  condition ht₁ ht₂ f hf g hg h →
  (∫ x, f x) ^ (1 - t) * (∫ y, g y) ^ t ≤ (1 - t) ^ (d * (1 - t)) * t ^ (d * t) * (∫ x, h x)

-- TODO: Check if this lemma is correct.
@[simp]
theorem volume_univ_zero_of_euclideanSpace_fin_zero :
    volume (@Set.univ (ℝn 0)) = 0 := by
  sorry

theorem prekopa_leindler_dim_zero
    {t : ℝ} (ht₁ : 0 < t) (ht₂ : t < 1)
    (f : ℝn 0 → ℝ) (hf : ∀ x, 0 ≤ f x)
    (g : ℝn 0 → ℝ) (hg : ∀ x, 0 ≤ g x)
    (h : ℝn 0 → ℝ) :
    prekopa_leindler_statement ht₁ ht₂ f hf g hg h := by
  intro h₁
  simp_rw [CharP.cast_eq_zero, zero_mul, Real.rpow_zero, mul_one, one_mul]
  simp only [integral_unique, smul_eq_mul]
  have h₃ : (volume (@Set.univ (ℝn 0))).toReal = 0 :=
    (toReal_eq_zero_iff (volume (@Set.univ (ℝn 0)))).mpr
      (.inl volume_univ_zero_of_euclideanSpace_fin_zero)
  simp only [h₃, zero_mul, Real.zero_rpow (Ne.symm (ne_of_lt ht₁)),
    Real.zero_rpow (Ne.symm (ne_of_lt (sub_pos_of_lt ht₂))), le_rfl]

theorem prekopa_leindler_dimension_sum
    {t : ℝ} (ht₁ : 0 < t) (ht₂ : t < 1)
    {d₁ : ℕ}
    (h₁ : ∀ {f : ℝn d₁ → ℝ} (hf : ∀ x, 0 ≤ f x) {g : ℝn d₁ → ℝ} (hg : ∀ x, 0 ≤ g x) {h : ℝn d₁ → ℝ},
      prekopa_leindler_statement ht₁ ht₂ f hf g hg h)
    {d₂ : ℕ}
    (h₂ : ∀ {f : ℝn d₂ → ℝ} (hf : ∀ x, 0 ≤ f x) {g : ℝn d₂ → ℝ} (hg : ∀ x, 0 ≤ g x) {h : ℝn d₂ → ℝ},
      prekopa_leindler_statement ht₁ ht₂ f hf g hg h)
    (f : ℝn (d₁ + d₂) → ℝ) (hf : ∀ x, 0 ≤ f x)
    (g : ℝn (d₁ + d₂) → ℝ) (hg : ∀ x, 0 ≤ g x)
    (h : ℝn (d₁ + d₂) → ℝ) :
    prekopa_leindler_statement ht₁ ht₂ f hf g hg h := by
  intro h₃
  sorry

theorem prekopa_leindler
    {t : ℝ} (ht₁ : 0 < t) (ht₂ : t < 1) {d : ℕ}
    (f : ℝn d → ℝ) (hf : ∀ x, 0 ≤ f x)
    (g : ℝn d → ℝ) (hg : ∀ x, 0 ≤ g x)
    (h : ℝn d → ℝ) :
    prekopa_leindler_statement ht₁ ht₂ f hf g hg h := by
  induction d using Nat.induction_on_sum
  case hzero => exact prekopa_leindler_dim_zero ht₁ ht₂ _ hf _ hg h
  case hone => sorry
  case ind h₂ d ih =>
    exact prekopa_leindler_dimension_sum ht₁ ht₂ (fun {_} hf {_} hg {h} ↦ h₂ _ hf _ hg h)
      (fun {_} hf {_} hg {h} ↦ ih _ hf _ hg h) f hf g hg h
