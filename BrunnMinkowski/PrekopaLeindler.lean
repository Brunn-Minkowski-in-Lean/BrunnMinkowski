import BrunnMinkowski.EuclideanSpace
import Mathlib

--open NNReal ENNReal MeasureTheory Finset
--open Real Set MeasureTheory Filter Asymptotics

--open scoped Real Topology

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

/-- A product dedicated for Euclidean space. -/
abbrev EuclideanProd
    (α : Type*) [AddCommGroup α] [TopologicalSpace α] [TopologicalAddGroup α] [T2Space α]
    [Module ℝ α] [ContinuousSMul ℝ α] [FiniteDimensional ℝ α]
    (β : Type*) [AddCommGroup β] [TopologicalSpace β] [TopologicalAddGroup β] [T2Space β]
    [Module ℝ β] [ContinuousSMul ℝ α] [FiniteDimensional ℝ β] :=
  WithLp 2 (α × β)

@[inherit_doc]
infixl:35 " ×ₑ " => EuclideanProd

namespace EuclideanSpace

variable {n₁ n₂ : ℕ}

open Fin Metric Nat Real
open ContinuousLinearEquiv MeasurableEquiv Topology

def finProdLinearEquiv (n₁ n₂ : ℕ) :
    ((EuclideanSpace ℝ (Fin n₁)) ×ₑ EuclideanSpace ℝ (Fin n₂)) ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin (n₁ + n₂)) :=
  .mk ⟨⟨fun ⟨a, b⟩ x ↦ if h : x < n₁
      then a (@Fin.ofNat' n₁ ⟨by omega⟩ x) else b (@Fin.ofNat' n₂ ⟨by omega⟩ (x - n₁)),
    fun ⟨_, _⟩ ⟨_, _⟩ ↦ by
      ext x; simp only [ofNat'_eq_cast, PiLp.add_apply]
      by_cases h : x < n₁ <;> simp only [h, ↓reduceDIte]⟩,
    fun r ⟨a, b⟩ ↦ by
      ext; simp only [ofNat'_eq_cast, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, mul_dite]⟩
    (fun x ↦ (fun x₁ ↦ x (@Fin.ofNat' (n₁ + n₂)
      ⟨match n₁ with | 0 => (isEmpty.false x₁).elim | _ + 1 => by omega⟩ x₁),
    fun x₂ ↦ x (@Fin.ofNat' (n₁ + n₂)
      ⟨match n₂ with | 0 => (isEmpty.false x₂).elim | _ + 1 => by omega⟩ (x₂ + n₁)))) (by
    rintro ⟨a, b⟩; simp only [ofNat'_eq_cast, val_natCast]; rw [Prod.mk.injEq]
    constructor <;> ext x
    · rw [dite_cond_eq_true]
      · congr; simp_rw [mod_eq_of_lt (lt_of_lt_of_le x.isLt (le_add_right _ n₂)), cast_val_eq_self]
      · simp only [mod_eq_of_lt (lt_of_lt_of_le x.isLt (le_add_right _ n₂)), x.isLt]
    · have h : x + n₁ < n₁ + n₂ := by omega
      rw [dite_cond_eq_false]
      · congr; simp_rw [mod_eq_of_lt h, Nat.add_sub_cancel, cast_val_eq_self]
      · rw [eq_iff_iff, iff_false, mod_eq_of_lt h]; omega) (by
      intro; ext x; simp only [ofNat'_eq_cast, val_natCast]
      by_cases h : x < n₁ <;> simp only [h, ↓reduceDIte] <;> congr
      · simp only [mod_eq_of_lt h, cast_val_eq_self]
      · have h₁ : x - n₁ < n₂ := by omega
        have h₂ : n₁ ≤ x := by omega
        simp_rw [mod_eq_of_lt h₁, Nat.sub_add_cancel h₂, cast_val_eq_self])

theorem add_finProdLinearEquiv
    (x₁ x₂ : EuclideanSpace ℝ (Fin n₁)) (x₃ x₄ : EuclideanSpace ℝ (Fin n₂)) :
    (finProdLinearEquiv n₁ n₂) (x₁, x₃) + (finProdLinearEquiv n₁ n₂) (x₂, x₄) =
    (finProdLinearEquiv n₁ n₂) (x₁ + x₂, x₃ + x₄) :=
  ((finProdLinearEquiv n₁ n₂).map_add _ _).symm

instance : T2Space ((EuclideanSpace ℝ (Fin n₁)) ×ₑ EuclideanSpace ℝ (Fin n₂)) where
  t2 x y h := by
    use ball x (dist x y / 2), ball y (dist x y / 2)
    simp only [isOpen_ball, dist_pos.mpr h, mem_ball, dist_self x, dist_self y, le_refl, and_true,
      div_pos_iff_of_pos_left, ofNat_pos, add_halves, ball_disjoint_ball]

def finProdLinearEquivIsOpenEmbedding
    (n₁ n₂ : ℕ) :
    IsOpenEmbedding (finProdLinearEquiv n₁ n₂) where
  eq_induced := sorry
  injective := sorry
  isOpen_range := sorry

def continuousFinProdLinearEquiv (n₁ n₂ : ℕ) : Continuous (finProdLinearEquiv n₁ n₂) where
  isOpen_preimage s h := by
    have := Set.preimage_equiv_eq_image_symm s (finProdLinearEquiv n₁ n₂).toEquiv
    simp only [LinearEquiv.coe_toEquiv, LinearEquiv.coe_toEquiv_symm, EquivLike.coe_coe] at this
    rw [this]
    sorry

def finProdContinuousLinearEquiv (n₁ n₂ : ℕ) :
    ((EuclideanSpace ℝ (Fin n₁)) ×ₑ (EuclideanSpace ℝ (Fin n₂))) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (n₁ + n₂)) :=
  LinearEquiv.toContinuousLinearEquivOfContinuous (finProdLinearEquiv n₁ n₂)
    (continuousFinProdLinearEquiv n₁ n₂)
--  ContinuousLinearEquiv.ofFinrankEq <| by simp [LinearEquiv.finrank_eq (WithLp.linearEquiv 2 _ _)]

theorem add_finProdContinuousLinearEquiv
    (x₁ x₂ : EuclideanSpace ℝ (Fin n₁)) (x₃ x₄ : EuclideanSpace ℝ (Fin n₂)) :
    (finProdContinuousLinearEquiv n₁ n₂) (x₁, x₃) + (finProdContinuousLinearEquiv n₁ n₂) (x₂, x₄) =
    (finProdContinuousLinearEquiv n₁ n₂) (x₁ + x₂, x₃ + x₄) :=
  ((finProdContinuousLinearEquiv n₁ n₂).map_add _ _).symm

instance : MeasurableSpace ((EuclideanSpace ℝ (Fin n₁)) ×ₑ EuclideanSpace ℝ (Fin n₂)) where
  MeasurableSet' s := MeasurableSet ((finProdLinearEquiv n₁ n₂) '' s)
  measurableSet_empty := by simp only [Set.image_empty, MeasurableSet.empty]
  measurableSet_compl s h := by
    have h₁ := Equiv.image_compl (finProdLinearEquiv n₁ n₂).toEquiv sᶜ
    simp at h₁; exact MeasurableSet.compl_iff.mp (h₁ ▸ h)
  measurableSet_iUnion f h := by simp only [Set.image_iUnion] at h ⊢; exact MeasurableSet.iUnion h

theorem measurable_finProdLinearEquiv {n₁ n₂ : ℕ} : Measurable (finProdLinearEquiv n₁ n₂) := by
  sorry

theorem measurable_finProdContinuousLinearEquiv
    {n₁ n₂ : ℕ} :
    Measurable (finProdContinuousLinearEquiv n₁ n₂) :=
  measurable_finProdLinearEquiv

noncomputable def finProdMeasurableEquiv' (n₁ n₂ : ℕ) :
    (EuclideanSpace ℝ (Fin n₁)) ×ₑ EuclideanSpace ℝ (Fin n₂) ≃ᵐ
      ((EuclideanSpace ℝ (Fin n₁)) × EuclideanSpace ℝ (Fin n₂)) :=
  ⟨Equiv.refl _, sorry, sorry⟩
  

noncomputable def finProdMeasurableEquiv (n₁ n₂ : ℕ) :
    ((EuclideanSpace ℝ (Fin n₁)) ×ₑ EuclideanSpace ℝ (Fin n₂)) ≃ᵐ
      EuclideanSpace ℝ (Fin (n₁ + n₂)) :=
  let eqv₀ := finProdMeasurableEquiv' n₁ n₂
  let eqv₁ : ((EuclideanSpace ℝ (Fin n₁)) × EuclideanSpace ℝ (Fin n₂)) ≃ᵐ
      (Fin n₁ → ℝ) × (Fin n₂ → ℝ) :=
    prodCongr (EuclideanSpace.measurableEquiv _) (EuclideanSpace.measurableEquiv _)
  let eqv₂ : ((Fin n₁ → ℝ) × (Fin n₂ → ℝ)) ≃ᵐ ((Fin n₁ ⊕ Fin n₂) → ℝ) :=
    (sumPiEquivProdPi fun _ ↦ ℝ).symm
  let eqv₃ : (((Fin n₁) ⊕ (Fin n₂)) → ℝ) ≃ᵐ ((Fin (n₁ + n₂)) → ℝ) :=
    piCongrLeft (fun _ ↦ ℝ) finSumFinEquiv
  let eqv₄ := (EuclideanSpace.measurableEquiv (Fin (n₁ + n₂))).symm
  eqv₀.trans (eqv₁.trans (eqv₂.trans (eqv₃.trans eqv₄)))

theorem injective_finProdMeasurableEquiv (n₁ n₂ : ℕ) :
    Function.Injective (finProdMeasurableEquiv n₁ n₂) := by
  intro _ _ _; simp_all only [EmbeddingLike.apply_eq_iff_eq]

theorem finProdMeasurableEmbedding (n₁ n₂ : ℕ) :
    MeasurableEmbedding (finProdMeasurableEquiv n₁ n₂) := by
  constructor <;> simp [injective_finProdMeasurableEquiv, MeasurableEquiv.measurable]

-- -- Likely false.
-- noncomputable def finProdLinearIsometryEquiv (n₁ n₂ : ℕ) :
--     ((EuclideanSpace ℝ (Fin n₁)) × (EuclideanSpace ℝ (Fin n₂))) ≃ₗᵢ[ℝ]
--       EuclideanSpace ℝ (Fin (n₁ + n₂)) :=
--   LinearIsometryEquiv.mk (finProdLinearEquiv n₁ n₂) fun ⟨x₁, x₂⟩ ↦ by
--     sorry

-- -- Likely false.
-- noncomputable instance {n₁ n₂ : ℕ} :
--     InnerProductSpace ℝ ((EuclideanSpace ℝ (Fin n₁)) × (EuclideanSpace ℝ (Fin n₂))) where
--   inner x y := (inner x.1 y.1) + (inner x.2 y.2)
--   norm_sq_eq_inner x := by
--     rcases x with ⟨x, y⟩
--     simp
--     sorry
--   conj_symm := sorry
--   add_left := sorry
--   smul_left := sorry

-- -- Likely fasle.
-- noncomputable def finProdOrthonormalBasis (n₁ n₂ : ℕ) :
--     OrthonormalBasis (Fin (n₁ + n₂)) ℝ
--       ((EuclideanSpace ℝ (Fin n₁)) × (EuclideanSpace ℝ (Fin n₂))) :=
--   ⟨sorry⟩

-- -- Likely false.
-- -- TODO: Remove `sorry`.
-- theorem finProdMeasurePreserving (n₁ n₂ : ℕ) :
--     MeasurePreserving (finProdMeasurableEquiv n₁ n₂) := by
--   -- rcases measurePreserving_symm volume (finProdMeasurableEquiv n₁ n₂).symm
--   --   with ⟨h₁, -⟩
--   -- refine ⟨h₁, ?_⟩
--   -- simp only [MeasurableEquiv.symm_symm] at *
--   apply OrthonormalBasis.measurePreserving_measurableEquiv
--   sorry

-- Likely false.
-- theorem finProdMeasurePreserving_symm (n₁ n₂ : ℕ) :
--     MeasurePreserving (finProdMeasurableEquiv n₁ n₂).symm :=
--   (finProdMeasurePreserving n₁ n₂).symm _

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
    MeasureTheory.MeasureSpace.volume (@Set.univ (Fin 0 → ℝ)) = 1 := by
  simp only [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_empty_univ]

open EuclideanSpace in
@[simp]
theorem volume_univ_one_of_euclideanSpace_fin_zero :
    MeasureTheory.MeasureSpace.volume (@Set.univ (EuclideanSpace ℝ (Fin 0))) = 1 :=
  let eqv := EuclideanSpace.measurableEquiv (Fin 0)
  have h₁ : MeasureTheory.MeasureSpace.volume (eqv ⁻¹' (@Set.univ (Fin 0 → ℝ))) = MeasureTheory.MeasureSpace.volume (@Set.univ (Fin 0 → ℝ)) :=
    MeasureTheory.MeasurePreserving.measure_preimage_equiv (volume_preserving_measurableEquiv (Fin 0)) _
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
  have h₃ : (MeasureTheory.MeasureSpace.volume (@Set.univ (ℝn 0))).toReal = 1 :=
    (ENNReal.toReal_eq_one_iff _).mpr volume_univ_one_of_euclideanSpace_fin_zero
  simp_rw [@MeasureTheory.integral_unique (ℝn 0) ℝ _ _ _ _ MeasureTheory.MeasureSpace.volume EuclideanSpace.zeroUnique, h₃, smul_eq_mul,
    one_mul, ge_iff_le]; simp only [default]
  have h₄ := h₁ 0 0; simp only [add_zero] at h₄; exact h₄

--open NNReal ENNReal MeasureTheory Finset
--open Real Set MeasureTheory Filter Asymptotics

theorem integral_integral_euclideanSpace
    {n₁ n₂ : ℕ} (f : EuclideanSpace ℝ (Fin n₁) → EuclideanSpace ℝ (Fin n₂) → ℝ)
    (hf : MeasureTheory.Integrable (Function.uncurry f) MeasureTheory.MeasureSpace.volume) :
    ∫ (x : EuclideanSpace ℝ (Fin n₁)), ∫ (y : EuclideanSpace ℝ (Fin n₂)), f x y ∂MeasureTheory.MeasureSpace.volume ∂MeasureTheory.MeasureSpace.volume =
    ∫ (z : EuclideanSpace ℝ (Fin (n₁ + n₂))),
      (let ⟨z₁, z₂⟩ := (EuclideanSpace.finProdMeasurableEquiv n₁ n₂).symm z; f z₁ z₂) ∂MeasureTheory.MeasureSpace.volume := by
  rw [MeasureTheory.integral_integral hf]
  have := @MeasureTheory.integral_map_equiv _ _ _ _ _ MeasureTheory.MeasureSpace.volume _ _
    (EuclideanSpace.finProdMeasurableEquiv n₁ n₂).symm fun z ↦ f z.1 z.2
  --simp_rw [Equiv.toFun_as_coe, MeasurableEquiv.coe_toEquiv, ← this,
  --  ← MeasureTheory.Measure.volume_eq_prod]
  --congr; symm; exact (EuclideanSpace.finProdMeasurePreserving_symm n₁ n₂).2
  sorry

theorem integral_integral_euclideanSpace'
    {n₁ n₂ : ℕ} (f : (EuclideanSpace ℝ (Fin n₁)) × EuclideanSpace ℝ (Fin n₂) → ℝ)
    (hf : MeasureTheory.Integrable f MeasureTheory.MeasureSpace.volume) :
    ∫ (x : EuclideanSpace ℝ (Fin n₁)), ∫ (y : EuclideanSpace ℝ (Fin n₂)), f (x, y) ∂MeasureTheory.MeasureSpace.volume ∂MeasureTheory.MeasureSpace.volume =
    ∫ (z : EuclideanSpace ℝ (Fin (n₁ + n₂))),
      f ((EuclideanSpace.finProdMeasurableEquiv n₁ n₂).symm z) ∂MeasureTheory.MeasureSpace.volume :=
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
  let F (x₁ : ℝn d₁) : ℝn d₂ → ℝ := fun x₂ ↦ f ((finProdContinuousLinearEquiv d₁ d₂) (x₁, x₂))
  let G (x₁ : ℝn d₁) : ℝn d₂ → ℝ := fun x₂ ↦ g ((finProdContinuousLinearEquiv d₁ d₂) (x₁, x₂))
  let H (x₁ : ℝn d₁) : ℝn d₂ → ℝ := fun x₂ ↦ h ((finProdContinuousLinearEquiv d₁ d₂) (x₁, x₂))
  have hF : ∀ {x₁} x₂, 0 ≤ F x₁ x₂ := fun _ ↦ hf _
  have hG : ∀ {x₁} x₂, 0 ≤ G x₁ x₂ := fun _ ↦ hg _
  have h₄ : ∀ x₁ y₁ : ℝn d₁, Condition ht₁ ht₂ (F x₁) hF (G y₁) hG (H (x₁ + y₁)) := by
    intro _ _ _ _
    simp only [F, G, H, ← add_finProdContinuousLinearEquiv]
    exact h₃ _ _
  have h₅ : Condition ht₁ ht₂
      (fun x ↦ ∫ x₂, F x x₂) (fun _ ↦ MeasureTheory.integral_nonneg hF)
      (fun y ↦ ∫ y₂, G y y₂) (fun _ ↦ MeasureTheory.integral_nonneg hG)
      (fun z ↦ (1 - t) ^ (d₂ * (1 - t)) * t ^ (d₂ * t) * ∫ z₂, H z z₂) := fun x₁ y₁ ↦
    h₂ hF hG (h₄ x₁ y₁)
  have h₆ := h₁ (fun _ ↦ MeasureTheory.integral_nonneg hF) (fun _ ↦ MeasureTheory.integral_nonneg hG) h₅
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
