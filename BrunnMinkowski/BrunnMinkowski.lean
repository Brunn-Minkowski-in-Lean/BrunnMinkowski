import Mathlib.Analysis.Convex.Body
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import BrunnMinkowski.EuclideanSpace
import BrunnMinkowski.PrekopaLeindler

open scoped Pointwise NNReal

variable {I : Type} [Fintype I] {n : ℕ}

noncomputable def ConvexBody.volume (A : ConvexBody (ℝI I)) : NNReal :=
  (MeasureTheory.volume (A : Set (ℝI I))).toNNReal

-- The underlying set of ConvexBody has finite volume
lemma convbody_set_vol_ne_top (A : ConvexBody (ℝI I)) :
    MeasureTheory.volume (A : Set (ℝI I)) ≠ ⊤ := by
  apply lt_top_iff_ne_top.mp
  apply Bornology.IsBounded.measure_lt_top A.isBounded

-- Convert x to ConvexBody {x}
noncomputable def singleton_to_convbody (x : ℝn n) : ConvexBody (ℝn n) :=
  { carrier := {x},
    convex' := convex_singleton x,
    isCompact' := isCompact_singleton,
    nonempty' := Set.singleton_nonempty x }

lemma convbody_vol_le_vol_add_right (A B: ConvexBody (ℝn n)) :
  A.volume ≤ (A + B).volume := by
  obtain ⟨b, hb⟩ := B.nonempty
  calc
    A.volume
      = (A + singleton_to_convbody b).volume := by
      simp [ConvexBody.volume]
      apply (ENNReal.toNNReal_eq_toNNReal_iff'
        (convbody_set_vol_ne_top A)
        (convbody_set_vol_ne_top (A + singleton_to_convbody b))).mpr
      simp [singleton_to_convbody]
    _ ≤ (A + B).volume := by
      simp [ConvexBody.volume]
      apply ENNReal.toNNReal_mono
      · exact convbody_set_vol_ne_top (A + B)
      · apply MeasureTheory.measure_mono
        apply Set.add_subset_add_left
        simp_all [singleton_to_convbody, SetLike.mem_coe]

-- Brunn-Minkowski inequality
theorem brunn_minkowski (A B : ConvexBody (ℝn n)) (ngz : n ≠ 0) :
    A.volume ^ (n⁻¹ : ℝ) + B.volume ^ (n⁻¹ : ℝ) ≤
    (A + B).volume ^ (n⁻¹ : ℝ) := by

  -- Assume n is nonzero
  let ninv := (n⁻¹ : ℝ)
  have hn_mul_ninv_eq_one : (n : ℝ) * ninv = 1 := by simp [ninv, ngz]

  let Avol := A.volume
  let Bvol := B.volume

  by_cases hAvol_zero : A.volume = 0
  · -- Assume A.volume = 0
    simp [hAvol_zero, ngz]
    rw [add_comm, NNReal.rpow_le_rpow_iff]
    exact convbody_vol_le_vol_add_right B A
    positivity
  by_cases hBvol_zero : B.volume = 0
  · -- Assume B.volume = 0
    simp [hBvol_zero, ngz]
    rw [NNReal.rpow_le_rpow_iff]
    exact convbody_vol_le_vol_add_right A B
    positivity
  -- Now assume A.volume ≠ 0 and B.volume ≠ 0
  rename' hAvol_zero => hAvol_nonzero, hBvol_zero => hBvol_nonzero
  have hAvol_pos : 0 < Avol := by positivity
  have hBvol_pos : 0 < Bvol := by positivity
  have hABsumvol_pos : 0 < (A + B).volume :=
    lt_of_lt_of_le (pos_iff_ne_zero.mpr hAvol_nonzero) (convbody_vol_le_vol_add_right A B)

  have hAvol_pow_ninv_pos : 0 < Avol ^ ninv := NNReal.rpow_pos hAvol_pos
  have hBvol_pow_ninv_pos : 0 < Bvol ^ ninv := NNReal.rpow_pos hBvol_pos

  have prekopa_leindler_special_case {t : ℝ} (h0t : 0 < t) (ht1 : t < 1) :
        Avol ^ (1 - t) * Bvol ^ t
        ≤ ((1 - t) ^ (1 - t) * t ^ t) ^ n * (A + B).volume
      := by
      -- Define the indicator functions on A, B, and A + B
      let ind_A : (ℝn n) → ℝ := (A : Set (ℝn n)).indicator 1
      let ind_B : (ℝn n) → ℝ := (B : Set (ℝn n)).indicator 1
      let ind_ABsum : (ℝn n) → ℝ := (A + B : Set (ℝn n)).indicator 1

      -- Check the indicator functions satisfy the condition of Prékopa-Leindler
      have hind_cond (x y : ℝn n) : (ind_A x) ^ (1 - t) * (ind_B y) ^ t
          ≤ ind_ABsum (x + y) := by
        by_cases hx_nin_A : x ∉ A
        · -- Assume x ∉ A
          simp [ind_A, hx_nin_A]
          rw [Real.zero_rpow (by simp [ne_of_gt, ht1])]
          simp [ind_ABsum, Set.indicator_apply_nonneg]
        by_cases hy_nin_B : y ∉ B
        · -- Assume y ≠ B
          simp [ind_B, hy_nin_B]
          rw [Real.zero_rpow (by exact ne_of_gt h0t)]
          simp [ind_ABsum, Set.indicator_apply_nonneg]
        -- Now assume x ∈ A and y ∈ B
        have hx_in_A : x ∈ A := by contrapose hx_nin_A; simp [hx_nin_A]
        have hy_in_B : y ∈ B := by contrapose hy_nin_B; simp [hy_nin_B]
        have hxy_in_ABsum : x + y ∈ (A + B : Set (ℝn n)) := by
          rw [Set.mem_add]
          exact ⟨x, hx_in_A, y, hy_in_B, rfl⟩

        simp [ind_A, ind_B, ind_ABsum, hx_in_A, hy_in_B, hxy_in_ABsum]

      have prekopa_leinler_app := prekopa_leindler h0t ht1
          ind_A ind_B ind_ABsum hind_cond

      -- ∫ indicator function of C = C.volume
      have hind_ConvBody_int_eq_vol (C : ConvexBody (ℝn n)) {f : (ℝn n) → ℝ} :
          f = (C : Set (ℝn n)).indicator 1 →
          ∫ x, f x = C.volume := by
        intro hf
        rw [hf, MeasureTheory.integral_indicator_one]
        simp [ConvexBody.volume, ENNReal.coe_toNNReal_eq_toReal]
        apply IsCompact.measurableSet C.isCompact

      -- Modify the special case of Prékopa–Leindler
      simp [ind_A, ind_B, ind_ABsum] at prekopa_leinler_app
      rw [hind_ConvBody_int_eq_vol A (by rfl),
        hind_ConvBody_int_eq_vol B (by rfl),
        hind_ConvBody_int_eq_vol (A + B) (by rfl)] at prekopa_leinler_app

      -- Modify the goal
      rw [mul_pow,
        ← Real.rpow_mul_natCast (by simp; exact le_of_lt ht1),
        ← Real.rpow_mul_natCast (by positivity)]
      simpa [mul_comm] using prekopa_leinler_app

  -- Prepare θ as an input in t
  let θ : ℝ := Bvol ^ ninv / (Avol ^ ninv + Bvol ^ ninv)

  have hone_minus_θ : 1 - θ = Avol ^ ninv / (Avol ^ ninv + Bvol ^ ninv)
    := by field_simp [θ]

  have hθ : 0 < θ ∧ θ < 1 := by
    unfold θ
    constructor
    · -- 0 < θ
      positivity
    · -- θ < 1
      have hhh: 0 < (Avol : ℝ) ^ ninv + (Bvol : ℝ) ^ ninv := by positivity
      simp [div_lt_one hhh]
      positivity

  -- Modify the special case of Prékopa–Leindler
  have prekopa_leindler_special_case' := prekopa_leindler_special_case hθ.1 hθ.2

  have hcoeff_simp : (1 - θ) ^ (1 - θ) * (θ) ^ (θ)
      = (Avol ^ ninv) ^ (1 - θ) * (Bvol ^ ninv) ^ (θ)
        / (Avol ^ ninv + Bvol ^ ninv)
    := by
    conv_lhs =>
      congr
      · congr; simp [hone_minus_θ]
      · congr; unfold θ
    field_simp [Real.div_rpow]
    rw [← Real.rpow_add]
    simp
    positivity

  rw [hcoeff_simp] at prekopa_leindler_special_case'

  have hAvol_toreal_nonneg : 0 ≤ (Avol : ℝ) := by positivity
  have hBvol_toreal_nonneg : 0 ≤ (Bvol : ℝ) := by positivity
  conv_rhs at prekopa_leindler_special_case' =>
    simp [div_pow, mul_pow]
    rw [← Real.rpow_mul hAvol_toreal_nonneg,
      ← Real.rpow_mul_natCast hAvol_toreal_nonneg,
      ← Real.rpow_mul hBvol_toreal_nonneg,
      ← Real.rpow_mul_natCast hBvol_toreal_nonneg]
    conv in (occs := 1 2) (ninv * _ * (n : ℝ)) =>
      all_goals rw [mul_comm, ← mul_assoc, hn_mul_ninv_eq_one, one_mul]

  field_simp at prekopa_leindler_special_case'
  unfold ninv at prekopa_leindler_special_case'

  -- Modify the goal
  apply le_of_pow_le_pow_left₀ ngz (le_of_lt (NNReal.rpow_pos hABsumvol_pos))
  simp [← NNReal.rpow_mul_natCast, inv_mul_cancel₀, ngz]

  apply (mul_le_mul_left (Real.rpow_pos_of_pos (NNReal.coe_pos.mpr hBvol_pos) θ)).mp
  apply (mul_le_mul_left (Real.rpow_pos_of_pos (NNReal.coe_pos.mpr hAvol_pos) (1 - θ))).mp

  simp [← mul_assoc]
  apply (le_div_iff₀ (pow_pos (by positivity) n)).mp

  exact prekopa_leindler_special_case'
