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

open ContinuousLinearEquiv MeasurableEquiv

noncomputable def finProdLinearEquiv (n₁ n₂ : ℕ) :
    ((EuclideanSpace ℝ (Fin n₁)) × (EuclideanSpace ℝ (Fin n₂))) ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin (n₁ + n₂)) :=
  LinearEquiv.ofFinrankEq _ _ <| by
  simp only [Module.finrank_prod, finrank_euclideanSpace, Fintype.card_fin]

theorem add_finProdLinearEquiv
    {n₁ n₂ : ℕ} (x₁ x₂ : EuclideanSpace ℝ (Fin n₁)) (x₃ x₄ : EuclideanSpace ℝ (Fin n₂)) :
    (finProdLinearEquiv n₁ n₂) (x₁, x₃) + (finProdLinearEquiv n₁ n₂) (x₂, x₄) =
    (finProdLinearEquiv n₁ n₂) (x₁ + x₂, x₃ + x₄) :=
  ((finProdLinearEquiv n₁ n₂).map_add _ _).symm

noncomputable def finProdContinuousLinearEquiv (n₁ n₂ : ℕ) :
    ((EuclideanSpace ℝ (Fin n₁)) × (EuclideanSpace ℝ (Fin n₂))) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (n₁ + n₂)) :=
  ContinuousLinearEquiv.ofFinrankEq <| by
  simp only [Module.finrank_prod, finrank_euclideanSpace, Fintype.card_fin]

theorem add_finProdContinuousLinearEquiv
    {n₁ n₂ : ℕ} (x₁ x₂ : EuclideanSpace ℝ (Fin n₁)) (x₃ x₄ : EuclideanSpace ℝ (Fin n₂)) :
    (finProdContinuousLinearEquiv n₁ n₂) (x₁, x₃) + (finProdContinuousLinearEquiv n₁ n₂) (x₂, x₄) =
    (finProdContinuousLinearEquiv n₁ n₂) (x₁ + x₂, x₃ + x₄) :=
  ((finProdContinuousLinearEquiv n₁ n₂).map_add _ _).symm

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

/-- A product dedicated for `EuclideanSpace`. -/
structure EuclideanProd
    (α : Type*) [AddCommGroup α] [TopologicalSpace α] [TopologicalAddGroup α] [T2Space α]
    [Module ℝ α] [ContinuousSMul ℝ α] [FiniteDimensional ℝ α]
    (β : Type*) [AddCommGroup β] [TopologicalSpace β] [TopologicalAddGroup β] [T2Space β]
    [Module ℝ β] [ContinuousSMul ℝ β] [FiniteDimensional ℝ β] where
  fst : α
  snd : β

@[inherit_doc]
infixr:35 " ×ₑ " => EuclideanProd

namespace EuclideanProd

open EuclideanSpace

variable {α : Type*} [AddCommGroup α] [TopologicalSpace α] [TopologicalAddGroup α] [T2Space α]
variable [Module ℝ α] [ContinuousSMul ℝ α] [FiniteDimensional ℝ α]
variable {β : Type*} [AddCommGroup β] [TopologicalSpace β] [TopologicalAddGroup β] [T2Space β]
variable [Module ℝ β] [ContinuousSMul ℝ β] [FiniteDimensional ℝ β]

instance : Zero (α ×ₑ β) :=
  ⟨0, 0⟩

instance : Add (α ×ₑ β) :=
  ⟨fun x y ↦ ⟨x.fst + y.fst, x.snd + y.snd⟩⟩

protected theorem ext (x y : α ×ₑ β) (h₁ : x.fst = y.fst) (h₂ : x.snd = y.snd) : x = y := by
  rcases x with ⟨x₁, x₂⟩; rcases y with ⟨y₁, y₂⟩; congr

instance : Zero (α ×ₑ β) :=
  ⟨0, 0⟩

section Zero

theorem zero_def : (0 : α ×ₑ β) = ⟨0, 0⟩ :=
  rfl

@[simp]
theorem zero_fst : (0 : α ×ₑ β).fst = 0 :=
  rfl

@[simp]
theorem zero_snd : (0 : α ×ₑ β).snd = 0 :=
  rfl

end Zero

instance : Add (α ×ₑ β) :=
  ⟨fun x y ↦ ⟨x.fst + y.fst, x.snd + y.snd⟩⟩

section Add

variable {x y : α ×ₑ β}
variable {a₁ a₂ : α} {b₁ b₂ : β}

theorem add_eq : x + y = ⟨x.fst + y.fst, x.snd + y.snd⟩ :=
  rfl

@[simp]
theorem add_eq' : EuclideanProd.mk a₁ b₁ + EuclideanProd.mk a₂ b₂ = ⟨a₁ + a₂, b₁ + b₂⟩ :=
  rfl

theorem add_fst : (x + y).fst = x.fst + y.fst :=
  rfl

theorem add_snd : (x + y).snd = x.snd + y.snd :=
  rfl

end Add

instance : Sub (α ×ₑ β) :=
  ⟨fun x y ↦ ⟨x.fst - y.fst, x.snd - y.snd⟩⟩

section Sub

variable {x y : α ×ₑ β}
variable {a₁ a₂ : α} {b₁ b₂ : β}

theorem sub_eq : x - y = ⟨x.fst - y.fst, x.snd - y.snd⟩ :=
  rfl

@[simp]
theorem sub_eq' : EuclideanProd.mk a₁ b₁ - EuclideanProd.mk a₂ b₂ = ⟨a₁ - a₂, b₁ - b₂⟩ :=
  rfl

theorem sub_fst : (x - y).fst = x.fst - y.fst :=
  rfl

theorem sub_snd : (x - y).snd = x.snd - y.snd :=
  rfl

end Sub

instance : Neg (α ×ₑ β) :=
  ⟨fun x ↦ ⟨-x.fst, -x.snd⟩⟩

section Neg

variable {x y : α ×ₑ β}
variable {a : α} {b : β}

theorem neg_eq : -x = ⟨-x.fst, -x.snd⟩ :=
  rfl

@[simp]
theorem neg_eq' : - EuclideanProd.mk a b = ⟨-a, -b⟩ :=
  rfl

end Neg

noncomputable instance : Norm (α ×ₑ β) :=
  ⟨fun x ↦ √ ((Euclidean.dist 0 x.fst) ^ 2 + (Euclidean.dist 0 x.snd) ^ 2)⟩

section Norm

variable {x : α ×ₑ β}
variable {a : α} {b : β}

theorem norm_eq : ‖x‖ = √ ((Euclidean.dist 0 x.fst) ^ 2 + (Euclidean.dist 0 x.snd) ^ 2) :=
  rfl

@[simp]
theorem norm_eq' :
    ‖EuclideanProd.mk a b‖ = √ ((Euclidean.dist 0 a) ^ 2 + (Euclidean.dist 0 b) ^ 2) :=
  rfl

end Norm

instance : SMul ℝ (α ×ₑ β) :=
  ⟨fun r x ↦ ⟨r • x.fst, r • x.snd⟩⟩

section SMul

variable {r : ℝ} {x : α ×ₑ β}
variable {a : α} {b : β}

theorem sMul_eq : r • x = ⟨r • x.fst, r • x.snd⟩ :=
  rfl

@[simp]
theorem sMul_eq' : r • EuclideanProd.mk a b = ⟨r • a, r • b⟩ :=
  rfl

end SMul

noncomputable instance : Dist (α ×ₑ β) :=
  ⟨fun x y ↦ √ ((Euclidean.dist x.fst y.fst) ^ 2 + (Euclidean.dist x.snd y.snd) ^ 2)⟩

section Dist

variable {x y : α ×ₑ β}
variable {a₁ a₂ : α} {b₁ b₂ : β}

theorem dist_def :
    dist x y = √ ((Euclidean.dist x.fst y.fst) ^ 2 + (Euclidean.dist x.snd y.snd) ^ 2) :=
  rfl

@[simp]
theorem dist_def' :
    dist (EuclideanProd.mk a₁ b₁) (EuclideanProd.mk a₂ b₂) =
    √ ((Euclidean.dist a₁ a₂) ^ 2 + (Euclidean.dist b₁ b₂) ^ 2) :=
  rfl

end Dist

instance : AddZeroClass (α ×ₑ β) where
  zero_add _ := by simp only [zero_def, add_eq, zero_add]
  add_zero _ := by simp only [zero_def, add_eq, add_zero]

instance : AddSemigroup (α ×ₑ β) where
  add_assoc _ _ _ := by simp only [add_eq, add_assoc]

instance : AddMonoid (α ×ₑ β) where
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec

instance : SubNegMonoid (α ×ₑ β) where
  sub_eq_add_neg _ _ := by simp only [sub_eq, neg_eq, add_eq, sub_eq_add_neg]
  zsmul z x := match z with
  | Int.ofNat n => AddMonoid.nsmul n x
  | Int.negSucc n => - AddMonoid.nsmul n.succ x

instance : AddGroup (α ×ₑ β) where
  neg_add_cancel _ := by
    simp only [add_eq, mk.injEq, zero_def, ← eq_neg_iff_add_eq_zero]; constructor <;> rfl

instance : AddCommMagma (α ×ₑ β) where
  add_comm _ _ := by simp only [add_eq, add_comm]

instance : AddCommSemigroup (α ×ₑ β) where
  add_comm _ _ := by simp only [add_eq, add_comm]

instance : AddCommMonoid (α ×ₑ β) where
  add_comm _ _ := by simp only [add_eq, add_comm]

instance : AddCommGroup (α ×ₑ β) where
  add_comm _ _ := by simp only [add_eq, add_comm]

instance : MulAction ℝ (α ×ₑ β) where
  one_smul _ := by simp only [sMul_eq, one_smul]
  mul_smul _ _ _ := by simp only [sMul_eq, mul_smul]

instance : DistribMulAction ℝ (α ×ₑ β) where
  smul_zero _ := by simp only [sMul_eq, zero_def, smul_zero]
  smul_add _ _ _ := by simp only [sMul_eq, smul_add, add_eq]

instance : Module ℝ (α ×ₑ β) where
  add_smul _ _ _ := by simp only [sMul_eq, add_smul, add_eq]
  zero_smul _ := by simp only [sMul_eq, zero_smul, zero_def]

noncomputable instance : PseudoMetricSpace (α ×ₑ β) where
  dist_self x := by simp [dist_def, Euclidean.dist, dist_self]
  dist_comm x y := by
    simp only [dist_def, Euclidean.dist]
    rw [dist_comm (toEuclidean x.fst), dist_comm (toEuclidean x.snd)]
  dist_triangle x y z := by
    simp only [dist_def, Euclidean.dist]
    rw [Real.sqrt_le_left (by positivity), add_sq', Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
    have h₁ := dist_triangle (toEuclidean x.fst) (toEuclidean y.fst) (toEuclidean z.fst)
    have h₂ := dist_triangle (toEuclidean x.snd) (toEuclidean y.snd) (toEuclidean z.snd)
    have h₃ := add_le_add (sq_le_sq' (by rw [neg_le_iff_add_nonneg]; positivity) h₁)
      (sq_le_sq' (by rw [neg_le_iff_add_nonneg]; positivity) h₂)
    apply le_trans h₃
    simp only [add_sq', ← sub_nonneg, sub_zero]; ring_nf
    apply ((@div_nonneg_iff ℝ _ _ 2).mp _).elim (fun h ↦ h.1) fun h ↦ False.elim (by norm_num at h)
    ring_nf
    rw [← neg_le_iff_add_nonneg', ← sq_le_sq₀ (by simp; positivity) (by positivity), mul_pow,
      Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), mul_add, add_mul, add_mul]
    rw [← sub_nonneg]; ring_nf; simp only [← mul_pow]
    refine le_trans (sq_nonneg (dist (toEuclidean x.fst) (toEuclidean y.fst) *
      dist (toEuclidean y.snd) (toEuclidean z.snd) - dist (toEuclidean y.fst) (toEuclidean z.fst) *
      dist (toEuclidean x.snd) (toEuclidean y.snd))) (le_of_eq ?_)
    ring

noncomputable instance : SeminormedAddCommGroup (α ×ₑ β) where
  dist_eq x y := by
    simp only [dist_def, ‖·‖]; unfold Euclidean.dist
    simp_rw [SeminormedAddCommGroup.dist_eq]
    simp only [map_zero, map_sub, zero_sub, sub_fst, sub_snd, norm_neg]

noncomputable instance : NormedSpace ℝ (α ×ₑ β) where
  norm_smul_le r x := sorry

instance : TopologicalSpace (α ×ₑ β) where
  IsOpen s := sorry
  isOpen_univ := sorry
  isOpen_inter := sorry
  isOpen_sUnion := sorry

noncomputable def finProdLinearEquiv
    (α : Type*) [AddCommGroup α] [TopologicalSpace α] [TopologicalAddGroup α] [T2Space α]
    [Module ℝ α] [ContinuousSMul ℝ α] [FiniteDimensional ℝ α]
    (β : Type*) [AddCommGroup β] [TopologicalSpace β] [TopologicalAddGroup β] [T2Space β]
    [Module ℝ β] [ContinuousSMul ℝ β] [FiniteDimensional ℝ β] :
    (α ×ₑ β) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ α + Module.finrank ℝ β)) :=
  ⟨IsLinearMap.mk' (fun ⟨a, b⟩ x ↦ if h : x < Module.finrank ℝ α
    then (toEuclidean a) (@Fin.ofNat' (Module.finrank ℝ α) (NeZero.of_gt h) x)
    else (toEuclidean b) (@Fin.ofNat' (Module.finrank ℝ β) (by
      rw [not_lt] at h
      have : x < Module.finrank ℝ α + Module.finrank ℝ β := Fin.is_lt _
      apply @NeZero.of_gt _ _ 0; omega) (x - Module.finrank ℝ α)))
   (IsLinearMap.mk
    (fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ ↦ sorry)
    (fun r ⟨a₂, b₂⟩ ↦ sorry)), sorry, sorry, sorry⟩

def finProdLinearEquiv' (n₁ n₂ : ℕ) :
    ((EuclideanSpace ℝ (Fin n₁)) ×ₑ EuclideanSpace ℝ (Fin n₂)) ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin (n₁ + n₂)) :=
  ⟨sorry, sorry, sorry, sorry⟩

end EuclideanProd

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

theorem integral_integral_euclideanSpace
    {n₁ n₂ : ℕ} (f : EuclideanSpace ℝ (Fin n₁) → EuclideanSpace ℝ (Fin n₂) → ℝ)
    (hf : Integrable (Function.uncurry f) volume) :
    ∫ (x : EuclideanSpace ℝ (Fin n₁)), ∫ (y : EuclideanSpace ℝ (Fin n₂)), f x y ∂volume ∂volume =
    ∫ (z : EuclideanSpace ℝ (Fin (n₁ + n₂))),
      (let ⟨z₁, z₂⟩ := (EuclideanSpace.finProdMeasurableEquiv n₁ n₂).symm z; f z₁ z₂) ∂volume := by
  rw [integral_integral hf]
  have := @MeasureTheory.integral_map_equiv _ _ _ _ _ volume _ _
    (EuclideanSpace.finProdMeasurableEquiv n₁ n₂).symm fun z ↦ f z.1 z.2
  simp_rw [Equiv.toFun_as_coe, MeasurableEquiv.coe_toEquiv, ← this,
    ← Measure.volume_eq_prod]
  congr; symm; exact (EuclideanSpace.finProdMeasurePreserving_symm n₁ n₂).2

theorem integral_integral_euclideanSpace'
    {n₁ n₂ : ℕ} (f : (EuclideanSpace ℝ (Fin n₁)) × EuclideanSpace ℝ (Fin n₂) → ℝ)
    (hf : Integrable f volume) :
    ∫ (x : EuclideanSpace ℝ (Fin n₁)), ∫ (y : EuclideanSpace ℝ (Fin n₂)), f (x, y) ∂volume ∂volume =
    ∫ (z : EuclideanSpace ℝ (Fin (n₁ + n₂))),
      f ((EuclideanSpace.finProdMeasurableEquiv n₁ n₂).symm z) ∂volume :=
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
