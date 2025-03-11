import BrunnMinkowski.EuclideanSpace
import Mathlib
import Mathlib.Tactic

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
    [Module ℝ β] [ContinuousSMul ℝ β] [FiniteDimensional ℝ β] :=
  WithLp 2 (α × β)

@[inherit_doc]
infixl:35 " ×ₑ " => EuclideanProd

namespace WithLp

variable {α β : Type*} {p : ENNReal}

instance [AddGroup α] [AddGroup β] : AddGroup (WithLp p (α × β)) :=
  @Prod.instAddGroup α β _ _

instance [TopologicalSpace α] [TopologicalSpace β] : TopologicalSpace (WithLp p (α × β)) :=
  inferInstance

instance
    [AddGroup α] [TopologicalSpace α] [TopologicalAddGroup α]
    [AddGroup β] [TopologicalSpace β] [TopologicalAddGroup β] :
    TopologicalAddGroup (WithLp p (α × β)) :=
  instTopologicalAddGroupSum

instance
    [TopologicalSpace α] [T2Space α] [TopologicalSpace β] [T2Space β] :
    T2Space (WithLp p (α × β)) :=
  Prod.t2Space

instance [TopologicalSpace α] [MeasurableSpace α] [TopologicalSpace β] [MeasurableSpace β] :
    MeasurableSpace (WithLp p (α × β)) :=
  Prod.instMeasurableSpace

noncomputable instance [MeasureTheory.MeasureSpace α] [MeasureTheory.MeasureSpace β] :
    MeasureTheory.MeasureSpace (WithLp p (α × β)) :=
  MeasureTheory.Measure.prod.measureSpace

theorem measurable_withlp {γ : Type*} [MeasurableSpace γ] :
    Measurable fun c : γ ↦ (c : WithLp p γ) :=
  fun ⦃_⦄ a ↦ a

end WithLp

namespace EuclideanSpace

variable {α : Type*} [AddCommGroup α] [TopologicalSpace α] [TopologicalAddGroup α] [T2Space α]
variable [Module ℝ α] [ContinuousSMul ℝ α] [FiniteDimensional ℝ α]
variable {β : Type*} [AddCommGroup β] [TopologicalSpace β] [TopologicalAddGroup β] [T2Space β]
variable [Module ℝ β] [ContinuousSMul ℝ β] [FiniteDimensional ℝ β]

variable {n₁ n₂ : ℕ}

open Fin Metric Nat Real
open ContinuousLinearEquiv MeasurableEquiv MeasureTheory Topology

instance zeroUnique : Unique (EuclideanSpace ℝ (Fin 0)) :=
  ⟨⟨0⟩, Subsingleton.eq_zero⟩

instance finrankZeroUnique (h : Module.finrank ℝ α = 0) : Unique α :=
  ⟨⟨0⟩, @Subsingleton.eq_zero _ _ (Module.finrank_zero_iff.mp h)⟩

instance {n : ℕ} : T2Space (EuclideanSpace ℝ (Fin n)) where
  t2 x y h := by
    use ball x (dist x y / 2), ball y (dist x y / 2)
    simp only [Metric.isOpen_ball, true_and]; simp [Metric.mem_ball_self, h]
    apply Metric.ball_disjoint_ball; simp

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

noncomputable def finProdContinuousLinearEquiv (n₁ n₂ : ℕ) :
    ((EuclideanSpace ℝ (Fin n₁)) ×ₑ (EuclideanSpace ℝ (Fin n₂))) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (n₁ + n₂)) :=
  ContinuousLinearEquiv.ofFinrankEq <| by
  simp [LinearEquiv.finrank_eq (WithLp.linearEquiv 2 _ _)]

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

noncomputable instance : MetricSpace ((EuclideanSpace ℝ (Fin n₁)) ×ₑ EuclideanSpace ℝ (Fin n₂)) :=
  inferInstance

theorem Fin.eq_of_ofNat'_eq_lt
    {n : ℕ} [NeZero n] {a b : ℕ} (ha : a < n) (hb : b < n) (h : Fin.ofNat' n a = Fin.ofNat' n b) :
    a = b := by
  simp only [ofNat'_eq_cast] at h
  simp_rw [← Fin.val_inj, val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  exact h

def finProdLinearIsometryEquiv (n₁ n₂ : ℕ) :
    ((EuclideanSpace ℝ (Fin n₁)) ×ₑ EuclideanSpace ℝ (Fin n₂)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n₁ + n₂)) :=
  ⟨finProdLinearEquiv n₁ n₂, fun x ↦ by
    simp only [finProdLinearEquiv, ofNat'_eq_cast, LinearEquiv.coe_mk, norm_eq, norm_eq_abs,
      sq_abs, cast_ofNat, WithLp.prod_norm_eq_of_nat 2 _ x, one_div]
    repeat rw [sq_sqrt (by positivity)]
    simp only [Real.sqrt_eq_rpow, one_div]; congr
    let s₁ : Finset (Fin (n₁ + n₂)) :=
      Finset.image (fun x : Fin n₁ ↦ @Fin.ofNat' _ ⟨by have := x.isLt; omega⟩ x.val) Finset.univ
    let s₂ := Finset.univ \ s₁
    have hs₂ : ∀ x ∈ s₂, n₁ ≤ x := by
      simp [s₂, s₁]; intro x hx; by_contra h'; simp at h'; exact hx ⟨x.val, h'⟩ (by simp)
    have h₁ : Disjoint s₁ s₂ := Finset.disjoint_sdiff
    have h₂ : Finset.univ = s₁ ∪ s₂ := by
      rw [Finset.union_comm, ← Finset.sdiff_union_inter Finset.univ s₁]
      congr; exact Finset.univ_inter _
    rw [h₂, Finset.sum_union h₁]
    have h₃ {a b c d : ℝ} : a = c → b = d → a + b = c + d := fun h₁ h₂ ↦ h₁ ▸ h₂ ▸ rfl
    apply h₃
    · rw [Finset.sum_image]
      · congr; ext a; 
        have h₄ := Nat.mod_eq_of_lt (lt_of_lt_of_le a.isLt
          (@_root_.le_add_right ℕ _ _ _ n₂ (le_refl n₁)))
        simp only [ofNat'_eq_cast, val_natCast, h₄, is_lt, ↓reduceDIte]
        congr; rcases x; simp only; congr; simp only [h₄, cast_val_eq_self]
      rintro a - b - h; simp only [s₁] at h
      exact Fin.eq_of_val_eq (@Fin.eq_of_ofNat'_eq_lt _ ⟨by omega⟩ _ _ (by omega) (by omega) h)
    · cases n₂
      case e_a.a.zero => simp [s₂, s₁]
      case e_a.a.succ n =>
        apply Finset.sum_nbij (fun x : Fin (n₁ + (n + 1)) ↦ Fin.ofNat' (n + 1) (x.val - n₁))
        · simp only [s₂, Finset.mem_sdiff, Finset.mem_univ, implies_true]
        · intro x₁ hx₁ x₂ hx₂ hx₃; simp only [ofNat'_eq_cast] at hx₃
          simp only [Finset.mem_coe] at hx₁ hx₂
          have : n₁ ≤ x₁ := hs₂ _ hx₁; have : n₁ ≤ x₂ := hs₂ _ hx₂
          have hx₄ : x₁.val - n₁ < n + 1 := (by omega); have hx₅ : x₂.val - n₁ < n + 1 := by omega
          have := Fin.eq_of_ofNat'_eq_lt hx₄ hx₅ hx₃; omega
        · rintro x -; simp [s₂, s₁]; use @Fin.ofNat' (n₁ + (n + 1)) ⟨by omega⟩ (x.val + n₁); simp
          constructor
          · intro y hy; haveI {a b : ℕ} : NeZero (a + (b + 1)) := ⟨by omega⟩
            have := Fin.eq_of_ofNat'_eq_lt (lt_of_lt_of_le y.isLt (le_add_right _ (n + 1)))
              (by omega) hy
            omega
          have : x.val + n₁ < n₁ + (n + 1) := by omega
          rw [Nat.mod_eq_of_lt this, Nat.add_sub_cancel, cast_val_eq_self]
        intro _ h; simp only [Nat.not_lt_of_le (hs₂ _ h)]; rfl⟩

def finProdLinearIsometryEquiv' (n₁ n₂ : ℕ) :
    ((EuclideanSpace ℝ (Fin n₁)) ×ₑ EuclideanSpace ℝ (Fin n₂)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n₁ + n₂)) :=
  sorry

theorem add_finProdLinearIsometryEquiv
    (x₁ x₂ : EuclideanSpace ℝ (Fin n₁)) (x₃ x₄ : EuclideanSpace ℝ (Fin n₂)) :
    (finProdLinearIsometryEquiv n₁ n₂) (x₁, x₃) + (finProdLinearIsometryEquiv n₁ n₂) (x₂, x₄) =
    (finProdLinearIsometryEquiv n₁ n₂) (x₁ + x₂, x₃ + x₄) :=
  ((finProdLinearIsometryEquiv n₁ n₂).map_add _ _).symm

instance : MeasurableSpace (α ×ₑ β) :=
  borel (α ×ₑ β)

instance instWithLpBorelSpace : BorelSpace (α ×ₑ β) :=
  ⟨rfl⟩

-- instance : MeasurableSpace ((EuclideanSpace ℝ (Fin n₁)) ×ₑ EuclideanSpace ℝ (Fin n₂)) :=
--   borel ((EuclideanSpace ℝ (Fin n₁)) ×ₑ EuclideanSpace ℝ (Fin n₂))

-- instance : BorelSpace ((EuclideanSpace ℝ (Fin n₁)) ×ₑ EuclideanSpace ℝ (Fin n₂)) :=
--   ⟨rfl⟩

-- def finProdMeasurableEquiv (n₁ n₂ : ℕ) :
--     ((EuclideanSpace ℝ (Fin n₁)) ×ₑ EuclideanSpace ℝ (Fin n₂)) ≃ᵐ
--       EuclideanSpace ℝ (Fin (n₁ + n₂)) :=
--   LinearIsometryEquiv.toMeasureEquiv (finProdLinearIsometryEquiv n₁ n₂)

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
    (f : ℝn d → ℝ) (hf₁ : MeasureTheory.Integrable f) (hf₂ : ∀ x, 0 ≤ f x)
    (g : ℝn d → ℝ) (hg₁ : MeasureTheory.Integrable g) (hg₂ : ∀ x, 0 ≤ g x)
    (h : ℝn d → ℝ) (hh : MeasureTheory.Integrable h) : Prop :=
  ∀ x y : ℝn d, (f x) ^ (1 - t) * (g y) ^ t ≤ h (x + y)

theorem condition_nonneg
    {t : ℝ} (ht₁ : 0 < t) (ht₂ : t < 1) {d : ℕ}
    {f : ℝn d → ℝ} (hf₁ : MeasureTheory.Integrable f) (hf₂ : ∀ x, 0 ≤ f x)
    {g : ℝn d → ℝ} (hg₁ : MeasureTheory.Integrable g) (hg₂ : ∀ x, 0 ≤ g x)
    {h : ℝn d → ℝ} (hh : MeasureTheory.Integrable h)
    (h₀ : Condition ht₁ ht₂ _ hf₁ hf₂ _ hg₁ hg₂ h hh) {x : ℝn d} :
    0 ≤ h x := by
  refine le_trans ?_ (add_zero x ▸ h₀ x 0); have := hf₂ x; have := hg₂ 0; positivity

def prekopa_leindler_statement
    {t : ℝ} (ht₁ : 0 < t) (ht₂ : t < 1) (d : ℕ) : Prop :=
  (f : ℝn d → ℝ) → (hf₁ : MeasureTheory.Integrable f) → (hf₂ : ∀ x, 0 ≤ f x) →
  (g : ℝn d → ℝ) → (hg₁ : MeasureTheory.Integrable g) → (hg₂ : ∀ x, 0 ≤ g x) →
  (h : ℝn d → ℝ) → (hh : MeasureTheory.Integrable h) →
  Condition ht₁ ht₂ f hf₁ hf₂ g hg₁ hg₂ h hh →
  (∫ x, f x) ^ (1 - t) * (∫ y, g y) ^ t ≤ (1 - t) ^ (d * (1 - t)) * t ^ (d * t) * (∫ x, h x)

@[simp]
theorem volume_univ_one_of_pi_fin_zero :
    MeasureTheory.volume (@Set.univ (Fin 0 → ℝ)) = 1 := by
  simp only [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_empty_univ]

@[simp]
theorem volume_univ_one_of_euclideanSpace_fin_zero :
    MeasureTheory.volume (@Set.univ (EuclideanSpace ℝ (Fin 0))) = 1 :=
  let eqv := EuclideanSpace.measurableEquiv (Fin 0)
  have h₁ : MeasureTheory.volume (eqv ⁻¹' (@Set.univ (Fin 0 → ℝ))) = MeasureTheory.volume (@Set.univ (Fin 0 → ℝ)) :=
    MeasureTheory.MeasurePreserving.measure_preimage_equiv (EuclideanSpace.volume_preserving_measurableEquiv (Fin 0)) _
  h₁ ▸ volume_univ_one_of_pi_fin_zero

theorem prekopa_leindler_dim_zero
    {t : ℝ} (ht₁ : 0 < t) (ht₂ : t < 1) :
    prekopa_leindler_statement ht₁ ht₂ 0 := by
  intro f hf₁ hf₂ g hg₁ hg₂ h hh₁ h₁
  simp_rw [CharP.cast_eq_zero, zero_mul, Real.rpow_zero, mul_one, one_mul]
  have h₃ : (MeasureTheory.volume (@Set.univ (ℝn 0))).toReal = 1 :=
    (ENNReal.toReal_eq_one_iff _).mpr volume_univ_one_of_euclideanSpace_fin_zero
  simp_rw [@MeasureTheory.integral_unique (ℝn 0) ℝ _ _ _ _ MeasureTheory.volume EuclideanSpace.zeroUnique, h₃, smul_eq_mul,
    one_mul, ge_iff_le]; simp only [default]
  have h₄ := h₁ 0 0; simp only [add_zero] at h₄; exact h₄

--open NNReal ENNReal MeasureTheory Finset
--open Real Set MeasureTheory Filter Asymptotics

-- theorem integral_integral_euclideanSpace
--     {n₁ n₂ : ℕ} (f : EuclideanSpace ℝ (Fin n₁) → EuclideanSpace ℝ (Fin n₂) → ℝ)
--     (hf : MeasureTheory.Integrable (Function.uncurry f) MeasureTheory.volume) :
--     ∫ (x : EuclideanSpace ℝ (Fin n₁)), ∫ (y : EuclideanSpace ℝ (Fin n₂)), f x y ∂MeasureTheory.volume ∂MeasureTheory.volume =
--     ∫ (z : EuclideanSpace ℝ (Fin (n₁ + n₂))),
--       (let ⟨z₁, z₂⟩ := (EuclideanSpace.finProdMeasurableEquiv n₁ n₂).symm z; f z₁ z₂) ∂MeasureTheory.volume := by
--   rw [MeasureTheory.integral_integral hf]
--   have := @MeasureTheory.integral_map_equiv _ _ _ _ _ MeasureTheory.volume _ _
--     (EuclideanSpace.finProdMeasurableEquiv n₁ n₂).symm fun z ↦ f z.1 z.2
--   sorry

-- theorem integral_integral_euclideanSpace'
--     {n₁ n₂ : ℕ} (f : (EuclideanSpace ℝ (Fin n₁)) × EuclideanSpace ℝ (Fin n₂) → ℝ)
--     (hf : MeasureTheory.Integrable f MeasureTheory.volume) :
--     ∫ (x : EuclideanSpace ℝ (Fin n₁)), ∫ (y : EuclideanSpace ℝ (Fin n₂)), f (x, y) ∂MeasureTheory.volume ∂MeasureTheory.volume =
--     ∫ (z : EuclideanSpace ℝ (Fin (n₁ + n₂))),
--       f ((EuclideanSpace.finProdMeasurableEquiv n₁ n₂).symm z) ∂MeasureTheory.volume :=
--   integral_integral_euclideanSpace (Function.curry f) hf

-- example {d₁ d₂ : ℕ} {f : (EuclideanSpace ℝ (Fin (d₁ + d₂))) → ℝ} (hf : MeasureTheory.Integrable f) :
--     ∫ (x : EuclideanSpace ℝ (Fin d₁)), ∫ (y : EuclideanSpace ℝ (Fin d₂)), f (fun z ↦ if h : z < d₁ then x (@Fin.ofNat' d₁ ⟨by omega⟩ z) else y ((@Fin.ofNat' d₂ ⟨by omega⟩ (z.val - d₁)))) =
--     ∫ (z : EuclideanSpace ℝ (Fin (d₁ + d₂))), f z := by
--   sorry

-- theorem two_variable_integral_finProdLinearEquiv_eq
--     {d₁ d₂ : ℕ} {f : ℝn (d₁ + d₂) → ℝ} (hf : MeasureTheory.Integrable f) :
--     ∫ (x : ℝn d₁), ∫ (y : ℝn d₂), f ((EuclideanSpace.finProdLinearEquiv d₁ d₂) (x, y)) =
--     ∫ (z : ℝn (d₁ + d₂)), f z := by
--   rw [MeasureTheory.integral_integral]
--   · simp only [Prod.mk.eta]
--     nth_rw 1 [← MeasureTheory.integral_map]
--     · sorry
--     · sorry
--     sorry
--   apply MeasureTheory.Integrable.comp_measurable
--   · sorry
--   sorry

-- TODO: Prove THIS.
-- theorem two_variable_integral_finProdContinuousLinearEquiv_eq
--     {d₁ d₂ : ℕ} {f : ℝn (d₁ + d₂) → ℝ} (hf : MeasureTheory.Integrable f) :
--     ∫ (x : ℝn d₁) (y : ℝn d₂), f ((EuclideanSpace.finProdContinuousLinearEquiv d₁ d₂) (x, y)) =
--     ∫ (z : ℝn (d₁ + d₂)), f z := by
--   rw [MeasureTheory.integral_integral]
--   · simp only [Prod.mk.eta]
--     rw [← MeasureTheory.Measure.volume_eq_prod]
--     simp [EuclideanSpace.finProdContinuousLinearEquiv, EuclideanSpace.finProdLinearEquiv]
--
--     sorry
--   apply MeasureTheory.Integrable.comp_measurable
--   · simp only [Prod.mk.eta]
--     rw [← MeasureTheory.Measure.volume_eq_prod]
--     sorry
--   sorry

instance : BorelSpace ((EuclideanSpace ℝ (Fin n₁)) ×ₑ (EuclideanSpace ℝ (Fin n₂))) :=
  sorry

noncomputable instance :
    NormedAddCommGroup ((EuclideanSpace ℝ (Fin n₁)) ×ₑ (EuclideanSpace ℝ (Fin n₂))) where

noncomputable instance :
    MeasureTheory.MeasureSpace ((EuclideanSpace ℝ (Fin n₁)) ×ₑ (EuclideanSpace ℝ (Fin n₂))) :=
  measureSpaceOfInnerProductSpace

section

open MeasureTheory

variable {α : Type*} [AddCommGroup α] [TopologicalSpace α] [TopologicalAddGroup α] [T2Space α]
variable [Module ℝ α] [ContinuousSMul ℝ α] [FiniteDimensional ℝ α]
variable {β : Type*} [AddCommGroup β] [TopologicalSpace β] [TopologicalAddGroup β] [T2Space β]
variable [Module ℝ β] [ContinuousSMul ℝ β] [FiniteDimensional ℝ β]

theorem measurable_slice_left
    [MeasureSpace α] [MeasureSpace β]
    (f : α ×ₑ β → ℝ) (hf : Measurable f) {a : α} :
    Measurable fun b ↦ f (a, b) :=
  Measurable.comp hf measurable_prod_mk_left

-- theorem measurable_slice_left_uncurry
--    [MeasureTheory.MeasureSpace α] [MeasureTheory.MeasureSpace β]
--    (f : α → β → ℝ) (hf : Measurable fun ((a, b) : α ×ₑ β) ↦ f a b) {a : α} :
--    Measurable fun b ↦ f a b :=
--  Measurable.of_uncurry_left hf

theorem aestronglyMeasurable_slice_left
    [MeasureSpace α] [MeasureSpace β] [SFinite ‹MeasureSpace β›.volume]
    (f : α ×ₑ β → ℝ) (hf : AEStronglyMeasurable f) :
    ∀ᵐ (a : α), AEStronglyMeasurable fun b ↦ f (a, b) :=
  AEStronglyMeasurable.prod_mk_left hf

theorem measurable_slice_right
    [MeasureSpace α] [MeasureSpace β]
    (f : α ×ₑ β → ℝ) (hf : Measurable f) {b : β} :
    Measurable fun a ↦ f (a, b) :=
  Measurable.comp hf measurable_prod_mk_right

-- theorem measurable_slice_right_uncurry
--     [MeasureTheory.MeasureSpace α] [MeasureTheory.MeasureSpace β]
--     (f : α → β → ℝ) (hf : Measurable fun ((a, b) : α ×ₑ β) ↦ f a b) {b : β} :
--     Measurable fun a ↦ f a b :=
--   Measurable.of_uncurry_right hf

theorem withLp_volume_eq_prod [MeasureSpace α] [MeasureSpace β] :
    (MeasureTheory.volume : Measure (α ×ₑ β)) = (MeasureTheory.volume : Measure (α × β)) := by
  sorry

theorem aestronglyMeasurable_slice_right
    [MeasureSpace α] [MeasureSpace β] [SFinite ‹MeasureSpace α›.volume]
    (f : α ×ₑ β → ℝ) (hf : AEStronglyMeasurable f) :
    ∀ᵐ (b : β), AEStronglyMeasurable fun a ↦ f (a, b) := by
  rw [Measure.volume_eq_prod] at hf
  filter_upwards with b 
  refine ⟨fun a ↦ hf.mk f (a, b),
    hf.stronglyMeasurable_mk.comp_measurable (Measurable.of_uncurry_right fun ⦃_⦄ ↦ id), ?_⟩
  sorry

end

-- TODO: Remove `sorry`.
set_option maxHeartbeats 1000000000 in
open EuclideanSpace in
theorem prekopa_leindler_dimension_sum
    {t : ℝ} (ht₁ : 0 < t) (ht₂ : t < 1)
    {d₁ : ℕ} (h₁ : prekopa_leindler_statement ht₁ ht₂ d₁)
    {d₂ : ℕ} (h₂ : prekopa_leindler_statement ht₁ ht₂ d₂) :
    prekopa_leindler_statement ht₁ ht₂ (d₁ + d₂) := by
  intro f hf₁ hf₂ g hg₁ hg₂ h hh₁ h₃
  let F (x₁ : ℝn d₁) : ℝn d₂ → ℝ := fun x₂ ↦ f ((finProdLinearIsometryEquiv d₁ d₂) (x₁, x₂))
  let F' : (ℝn d₁ ×ₑ ℝn d₂) → ℝ := f ∘ (finProdLinearIsometryEquiv d₁ d₂)
  let G (y₁ : ℝn d₁) : ℝn d₂ → ℝ := fun y₂ ↦ g ((finProdLinearIsometryEquiv d₁ d₂) (y₁, y₂))
  let G' : (ℝn d₁ ×ₑ ℝn d₂) → ℝ := g ∘ (finProdLinearIsometryEquiv d₁ d₂)
  let H (z₁ : ℝn d₁) : ℝn d₂ → ℝ := fun z₂ ↦ h ((finProdLinearIsometryEquiv d₁ d₂) (z₁, z₂))
  let H' : (ℝn d₁ ×ₑ ℝn d₂) → ℝ := h ∘ (finProdLinearIsometryEquiv d₁ d₂)
  
  -- have hF'₁ : MeasureTheory.Integrable F' (MeasureTheory.volume : MeasureTheory.Measure ((ℝn d₁) ×ₑ (ℝn d₂))) := by
  --   simp_rw [← MeasureTheory.integrable_comp (finProdLinearIsometryEquiv d₁ d₂)] at hf₁
  --   exact hf₁
  -- have hG'₁ : MeasureTheory.Integrable G' MeasureTheory.volume := by
  --   simp_rw [← MeasureTheory.integrable_comp (finProdLinearIsometryEquiv d₁ d₂)] at hg₁
  --   exact hg₁
  -- have hH'₁ : MeasureTheory.Integrable H' MeasureTheory.volume := by
  --   simp_rw [← MeasureTheory.integrable_comp (finProdLinearIsometryEquiv d₁ d₂)] at hh₁
  --   exact hh₁


  /-
  have h₃ : ∀ᵐ (x₁ : ℝn d₁) ∂MeasureTheory.volume, Condition ht₁ ht₂
      (fun x₁ ↦ ∫ x₂, F x₁ x₂) sorry (fun _ ↦ MeasureTheory.integral_nonneg (fun _ ↦ hf₂ _))
      (fun y₁ ↦ ∫ y₂, G y₁ y₂) sorry (fun _ ↦ MeasureTheory.integral_nonneg (fun _ ↦ hg₂ _))
      (fun z₁ ↦ (1 - t) ^ (d₂ * (1 - t)) * t ^ (d₂ * t) * ∫ z₂, H z₁ z₂) sorry :=
    sorry
  -/
  sorry
  -- have := measurable_slice_left_uncurry F
  -- simp [F, hf₀] at this
  -- let sF : Set (ℝn d₁) := {x | MeasureTheory.Integrable (F x)}
  -- let sG : Set (ℝn d₁) := {x | MeasureTheory.Integrable (G x)}
  -- let sH : Set (ℝn d₁) := {x | MeasureTheory.Integrable (H x)}
  -- have hF₁ : ∀ {x₁}, MeasureTheory.Integrable (F x₁) := sorry
  -- have hG₁ : ∀ {x₁}, MeasureTheory.Integrable (G x₁) := sorry
  -- have hH : ∀ {x₁}, MeasureTheory.Integrable (H x₁) := sorry
  -- have hF₂ : ∀ {x₁} x₂, 0 ≤ F x₁ x₂ := fun _ ↦ hf₂ _
  -- have hG₂ : ∀ {x₁} x₂, 0 ≤ G x₁ x₂ := fun _ ↦ hg₂ _
  -- have h₄ : ∀ x₁ y₁ : ℝn d₁, Condition ht₁ ht₂ (F x₁) hF₁ hF₂ (G y₁) hG₁ hG₂ (H (x₁ + y₁)) hH := by
  --   intro _ _ _ _
  --   simp only [F, G, H, ← add_finProdLinearIsometryEquiv]
  --   exact h₃ _ _
  -- have h₅ : Condition ht₁ ht₂
  --     (fun x ↦ ∫ x₂, F x x₂) sorry (fun _ ↦ MeasureTheory.integral_nonneg hF₂)
  --     (fun y ↦ ∫ y₂, G y y₂) sorry (fun _ ↦ MeasureTheory.integral_nonneg hG₂)
  --     (fun z ↦ (1 - t) ^ (d₂ * (1 - t)) * t ^ (d₂ * t) * ∫ z₂, H z z₂) sorry := fun x₁ y₁ ↦
  --   h₂ hF₁ hF₂ hG₁ hG₂ sorry (h₄ x₁ y₁)
  -- have h₆ := h₁ sorry (fun _ ↦ MeasureTheory.integral_nonneg hF₂) sorry (fun _ ↦ MeasureTheory.integral_nonneg hG₂) sorry h₅
  -- simp_rw [mul_comm _ (∫ z, _ ∂MeasureTheory.volume)] at h₆
  -- simp only [← smul_eq_mul, integral_smul_const] at h₆
  -- simp_rw [smul_eq_mul, ← mul_assoc] at h₆
  -- rw [mul_assoc (∫ x, _ ∂MeasureTheory.volume) ((1 - t) ^ _) (t ^ _)] at h₆
  -- rw [mul_assoc _ (_ * _) _, mul_assoc _ (_ * _) _, mul_comm ((1 - t) ^ _) (t ^ _),
  --   mul_comm _ (t ^ _), mul_assoc (t ^ _), ← mul_assoc (t ^ _), ← Real.rpow_add ht₁,
  --   ← Real.rpow_add (by linarith : 0 < 1 - t), mul_comm _ (t ^ _ * (1 - t) ^ _),
  --   mul_comm (t ^ _) ((1 - t) ^ _)] at h₆
  -- simp only [Nat.cast_add]; ring_nf at h₆ ⊢
  -- have h₇ :
  --     ∫ (x : ℝn d₁) (z₂ : ℝn d₂), h ((finProdContinuousLinearEquiv d₁ d₂) (x, z₂)) = ∫ x, h x :=
  --   sorry
  -- apply le_trans (le_of_eq _) (h₇ ▸ h₆)
  -- simp [F, G, H]
  -- sorry


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
