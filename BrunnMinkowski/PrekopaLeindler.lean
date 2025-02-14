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

/- UNUSED

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

-/

namespace EuclideanSpace

noncomputable def finProdLinearEquiv (n₁ n₂ : ℕ) :
    ((EuclideanSpace ℝ (Fin n₁)) × (EuclideanSpace ℝ (Fin n₂))) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (n₁ + n₂)) :=
  ContinuousLinearEquiv.ofFinrankEq <| by
  simp only [Module.finrank_prod, finrank_euclideanSpace, Fintype.card_fin]

theorem add_finProdLinearEquiv
    {n₁ n₂ : ℕ} (x₁ x₂ : EuclideanSpace ℝ (Fin n₁)) (x₃ x₄ : EuclideanSpace ℝ (Fin n₂)) :
    (finProdLinearEquiv n₁ n₂) (x₁, x₃) + (finProdLinearEquiv n₁ n₂) (x₂, x₄) =
    (finProdLinearEquiv n₁ n₂) (x₁ + x₂, x₃ + x₄) :=
  ((finProdLinearEquiv n₁ n₂).map_add (x₁, x₃) (x₂, x₄)).symm

open MeasurableEquiv in
noncomputable def finProdMeasurableEquiv (n₁ n₂ : ℕ) :
    ((EuclideanSpace ℝ (Fin n₁)) × (EuclideanSpace ℝ (Fin n₂))) ≃ᵐ
      EuclideanSpace ℝ (Fin (n₁ + n₂)) :=
  let eqv₁ : ((EuclideanSpace ℝ (Fin n₁)) × (EuclideanSpace ℝ (Fin n₂))) ≃ᵐ
      (Fin n₁ → ℝ) × (Fin n₂ → ℝ) :=
    prodCongr (EuclideanSpace.measurableEquiv _) (EuclideanSpace.measurableEquiv _)
  let eqv₂ : ((Fin n₁ → ℝ) × (Fin n₂ → ℝ)) ≃ᵐ ((Fin n₁ ⊕ Fin n₂) → ℝ) :=
    (sumPiEquivProdPi fun _ ↦ ℝ).symm
  let eqv₃ : (((Fin n₁) ⊕ (Fin n₂)) → ℝ) ≃ᵐ ((Fin (n₁ + n₂)) → ℝ) :=
    piCongrLeft (fun _ ↦ ℝ) finSumFinEquiv
  let eqv₄ := (EuclideanSpace.measurableEquiv (Fin (n₁ + n₂))).symm
  eqv₁.trans (eqv₂.trans (eqv₃.trans eqv₄))

end EuclideanSpace

/- UNUSED

noncomputable def EuclideanSpace.split
    (n₁ n₂ : ℕ) (x : EuclideanSpace ℝ (Fin (n₁ + n₂))) :
    EuclideanSpace ℝ (Fin n₁) × EuclideanSpace ℝ (Fin n₂) :=
  (EuclideanSpace.finProdLinearEquiv n₁ n₂).symm x

noncomputable def EuclideanSpace.split.front
    (n₁ n₂ : ℕ) (x : EuclideanSpace ℝ (Fin (n₁ + n₂))) :
    EuclideanSpace ℝ (Fin n₁) :=
  (EuclideanSpace.split n₁ n₂ x).1

noncomputable def EuclideanSpace.split.back
    (n₁ n₂ : ℕ) (x : EuclideanSpace ℝ (Fin (n₁ + n₂))) :
    EuclideanSpace ℝ (Fin n₂) :=
  (EuclideanSpace.split n₁ n₂ x).2

-- TODO: Consider not using it.
-- TODO: Consider higher level types if possible.
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

-/

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
def Condition
    {t : ℝ} (ht₁ : 0 < t) (ht₂ : t < 1) {d : ℕ}
    (f : ℝn d → ℝ) (hf : ∀ x, 0 ≤ f x)
    (g : ℝn d → ℝ) (hg : ∀ x, 0 ≤ g x)
    (h : ℝn d → ℝ) : Prop :=
  ∀ x y : ℝn d, (f x) ^ (1 - t) * (g y) ^ t ≤ h (x + y)

theorem condition_nonneg
    {t : ℝ} (ht₁ : 0 < t) (ht₂ : t < 1) {d : ℕ}
    {f : ℝn d → ℝ} (hf : ∀ x, 0 ≤ f x)
    {g : ℝn d → ℝ} (hg : ∀ x, 0 ≤ g x)
    {h : ℝn d → ℝ} (h₀ : Condition ht₁ ht₂ _ hf _ hg h) {x : ℝn d} :
    0 ≤ h x := by
  refine le_trans ?_ (add_zero x ▸ h₀ x 0); have := hf x; have := hg 0; positivity

def prekopa_leindler_statement
    {t : ℝ} (ht₁ : 0 < t) (ht₂ : t < 1) {d : ℕ}
    (f : ℝn d → ℝ) (hf : ∀ x, 0 ≤ f x)
    (g : ℝn d → ℝ) (hg : ∀ x, 0 ≤ g x)
    (h : ℝn d → ℝ) : Prop :=
  Condition ht₁ ht₂ f hf g hg h →
  (∫ x, f x) ^ (1 - t) * (∫ y, g y) ^ t ≤ (1 - t) ^ (d * (1 - t)) * t ^ (d * t) * (∫ x, h x)

@[simp]
theorem volume_univ_one_of_pi_fin_zero :
    volume (@Set.univ (Fin 0 → ℝ)) = 1 := by
  simp only [MeasureTheory.volume_pi, Measure.pi_empty_univ]

open EuclideanSpace in
@[simp]
theorem volume_univ_one_of_euclideanSpace_fin_zero :
    volume (@Set.univ (EuclideanSpace ℝ (Fin 0))) = 1 :=
  let eqv := EuclideanSpace.measurableEquiv (Fin 0)
  have h₁ : volume (eqv ⁻¹' (@Set.univ (Fin 0 → ℝ))) = volume (@Set.univ (Fin 0 → ℝ)) :=
    MeasurePreserving.measure_preimage_equiv (volume_preserving_measurableEquiv (Fin 0)) _
  h₁ ▸ volume_univ_one_of_pi_fin_zero

instance EuclideanSpace.zeroUnique : Unique (EuclideanSpace ℝ (Fin 0)) :=
  ⟨⟨0⟩, Subsingleton.eq_zero⟩

theorem prekopa_leindler_dim_zero
    {t : ℝ} (ht₁ : 0 < t) (ht₂ : t < 1)
    (f : ℝn 0 → ℝ) (hf : ∀ x, 0 ≤ f x)
    (g : ℝn 0 → ℝ) (hg : ∀ x, 0 ≤ g x)
    (h : ℝn 0 → ℝ) :
    prekopa_leindler_statement ht₁ ht₂ f hf g hg h := by
  intro h₁
  simp_rw [CharP.cast_eq_zero, zero_mul, Real.rpow_zero, mul_one, one_mul]
  have h₃ : (volume (@Set.univ (ℝn 0))).toReal = 1 :=
    (ENNReal.toReal_eq_one_iff _).mpr volume_univ_one_of_euclideanSpace_fin_zero
  simp_rw [@integral_unique (ℝn 0) ℝ _ _ _ _ volume EuclideanSpace.zeroUnique, h₃, smul_eq_mul,
    one_mul, ge_iff_le]; simp only [default]
  have h₄ := h₁ 0 0; simp only [add_zero] at h₄; exact h₄

-- TODO: Remove `sorry`.
theorem integral_integral_euclideanSpace
    {n₁ n₂ : ℕ} (f : EuclideanSpace ℝ (Fin n₁) → EuclideanSpace ℝ (Fin n₂) → ℝ)
    (hf : Integrable (Function.uncurry f) volume) :
    ∫ (x : EuclideanSpace ℝ (Fin n₁)), ∫ (y : EuclideanSpace ℝ (Fin n₂)), f x y ∂volume ∂volume =
    ∫ (z : EuclideanSpace ℝ (Fin (n₁ + n₂))),
      (let ⟨z₁, z₂⟩ := (EuclideanSpace.finProdLinearEquiv n₁ n₂).symm z; f z₁ z₂) ∂volume := by
  simp only [integral_integral hf, ContinuousLinearEquiv.symm, AddHom.toFun_eq_coe,
    LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
  sorry

theorem integral_integral_euclideanSpace'
    {n₁ n₂ : ℕ} (f : (EuclideanSpace ℝ (Fin n₁)) × EuclideanSpace ℝ (Fin n₂) → ℝ)
    (hf : Integrable f volume) :
    ∫ (x : EuclideanSpace ℝ (Fin n₁)), ∫ (y : EuclideanSpace ℝ (Fin n₂)), f (x, y) ∂volume ∂volume =
    ∫ (z : EuclideanSpace ℝ (Fin (n₁ + n₂))),
      f ((EuclideanSpace.finProdLinearEquiv n₁ n₂).symm z) ∂volume :=
  integral_integral_euclideanSpace (Function.curry f) hf

-- TODO: Remove `sorry`.
open EuclideanSpace in
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
  let F (x₁ : ℝn d₁) : ℝn d₂ → ℝ := fun x₂ ↦ f ((finProdLinearEquiv d₁ d₂) (x₁, x₂))
  let G (x₁ : ℝn d₁) : ℝn d₂ → ℝ := fun x₂ ↦ g ((finProdLinearEquiv d₁ d₂) (x₁, x₂))
  let H (x₁ : ℝn d₁) : ℝn d₂ → ℝ := fun x₂ ↦ h ((finProdLinearEquiv d₁ d₂) (x₁, x₂))
  have hF : ∀ {x₁} x₂, 0 ≤ F x₁ x₂ := fun _ ↦ hf _
  have hG : ∀ {x₁} x₂, 0 ≤ G x₁ x₂ := fun _ ↦ hg _
  have h₄ : ∀ x₁ y₁ : ℝn d₁, Condition ht₁ ht₂ (F x₁) hF (G y₁) hG (H (x₁ + y₁)) := by
    intro _ _ _ _
    simp only [F, G, H, ← add_finProdLinearEquiv]
    exact h₃ _ _
  have h₅ : Condition ht₁ ht₂
      (fun x ↦ ∫ x₂, F x x₂) (fun _ ↦ integral_nonneg hF)
      (fun y ↦ ∫ y₂, G y y₂) (fun _ ↦ integral_nonneg hG)
      (fun z ↦ (1 - t) ^ (d₂ * (1 - t)) * t ^ (d₂ * t) * ∫ z₂, H z z₂) := fun x₁ y₁ ↦
    h₂ hF hG (h₄ x₁ y₁)
  have h₆ := h₁ (fun _ ↦ integral_nonneg hF) (fun _ ↦ integral_nonneg hG) h₅
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
