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
      simp only [ConvexBody.volume, singleton_to_convbody, ConvexBody.coe_add,
        ConvexBody.coe_mk, Set.add_singleton, Set.image_add_right,
        MeasureTheory.measure_preimage_add_right]
    _ ≤ (A + B).volume := by
      simp only [ConvexBody.volume, ConvexBody.coe_add]
      apply ENNReal.toNNReal_mono
      · exact convbody_set_vol_ne_top (A + B)
      · apply MeasureTheory.measure_mono
        apply Set.add_subset_add_left
        simp only [singleton_to_convbody, ConvexBody.coe_mk,
          Set.singleton_subset_iff, hb]

-- Brunn-Minkowski inequality
theorem brunn_minkowski (A B : ConvexBody (ℝn n)) (ngz : n ≠ 0) :
    A.volume ^ (n⁻¹ : ℝ) + B.volume ^ (n⁻¹ : ℝ) ≤
    (A + B).volume ^ (n⁻¹ : ℝ) := by

  let ninv := (n⁻¹ : ℝ)
  set Avol := A.volume
  set Bvol := B.volume

  rcases eq_zero_or_pos Avol with hAvol | hAvol
  · -- Assume A.volume = 0
    simp only [hAvol, ne_eq, inv_eq_zero, Nat.cast_eq_zero, ngz,
      not_false_eq_true, NNReal.zero_rpow, zero_add, ge_iff_le, ninv]
    rw [add_comm, NNReal.rpow_le_rpow_iff (by positivity)]
    exact convbody_vol_le_vol_add_right B A
  rcases eq_zero_or_pos Bvol with hBvol | hBvol
  · -- Assume B.volume = 0
    simp only [hBvol, ne_eq, inv_eq_zero, Nat.cast_eq_zero, ngz,
      not_false_eq_true, NNReal.zero_rpow, ninv, add_zero, ge_iff_le]
    rw [NNReal.rpow_le_rpow_iff (by positivity)]
    exact convbody_vol_le_vol_add_right A B

  -- Now assume A.volume ≠ 0 and B.volume ≠ 0
  have hABsumvol_pos : 0 < (A + B).volume :=
    lt_of_lt_of_le hAvol (convbody_vol_le_vol_add_right A B)

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
          have h1_sub_t_lt_0 : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht1)
          simp only [ind_A, ind_ABsum,
            Set.indicator_of_not_mem hx_nin_A,
            Real.zero_rpow h1_sub_t_lt_0, zero_mul, Set.indicator_apply_nonneg,
            Pi.one_apply, zero_le_one, implies_true]
        by_cases hy_nin_B : y ∉ B
        · -- Assume y ∉ B
          simp only [ind_B ,ind_ABsum,
            Set.indicator_of_not_mem hy_nin_B,
            Real.zero_rpow (ne_of_gt h0t), mul_zero,
            Set.indicator_apply_nonneg, Pi.one_apply, zero_le_one, implies_true]
        -- Now assume x ∈ A and y ∈ B
        have hx_in_A : x ∈ A := of_not_not hx_nin_A
        have hy_in_B : y ∈ B := of_not_not hy_nin_B
        have hxy_sum_in_AB_sum : x + y ∈ (A + B : Set (ℝn n)) := by
          rw [Set.mem_add]
          exact ⟨x, hx_in_A, y, hy_in_B, rfl⟩

        simp only [ind_A, ind_B, ind_ABsum]
        iterate 3 rw [Set.indicator_of_mem _]
        rotate_left; exact hxy_sum_in_AB_sum; exact hy_in_B; exact hx_in_A
        norm_num

      -- Apply t = θ in Prékopa-Leindler
      have prekopa_leinler_app := prekopa_leindler h0t ht1
          ind_A ind_B ind_ABsum hind_cond

      -- ∫ indicator function of C = C.volume
      have hind_ConvBody_int_eq_vol (C : ConvexBody (ℝn n)) {f : (ℝn n) → ℝ} (hf : f = (C : Set (ℝn n)).indicator 1) :
          ∫ x, f x = C.volume := by
        rw [hf, MeasureTheory.integral_indicator_one]
        simp only [hf, MeasureTheory.integral_indicator_one,
          ConvexBody.volume, ENNReal.coe_toNNReal_eq_toReal]
        apply IsCompact.measurableSet C.isCompact

      -- Modify the special case of Prékopa–Leindler
      unfold ind_A ind_B ind_ABsum at prekopa_leinler_app
      rw [hind_ConvBody_int_eq_vol A (by rfl),
        hind_ConvBody_int_eq_vol B (by rfl),
        hind_ConvBody_int_eq_vol (A + B) (by rfl)] at prekopa_leinler_app

      -- Modify the goal
      rw [mul_pow,
        ← Real.rpow_mul_natCast (by rw [sub_nonneg]; exact le_of_lt ht1),
        ← Real.rpow_mul_natCast (by exact le_of_lt h0t)]
      simpa only [mul_comm] using prekopa_leinler_app

  -- Prepare θ as an input in t
  set θ : ℝ := Bvol ^ ninv / (Avol ^ ninv + Bvol ^ ninv)

  have hone_minus_θ : 1 - θ = Avol ^ ninv / (Avol ^ ninv + Bvol ^ ninv) := by
    have : (Avol : ℝ) ^ ninv + (Bvol : ℝ) ^ ninv ≠ 0 := by positivity
    rw [eq_div_iff this, sub_mul, div_mul_cancel₀ _ this, one_mul,
      add_sub_cancel_right]

  have hθ : 0 < θ ∧ θ < 1 := by
    constructor
    · -- 0 < θ
      positivity
    · -- θ < 1
      rw [div_lt_one (by positivity), lt_add_iff_pos_left]
      positivity

  -- Modify the special case of Prékopa–Leindler with t = θ
  have prekopa_leindler_special_case_θ :=
    prekopa_leindler_special_case hθ.1 hθ.2

  have : (1 - θ) ^ (1 - θ) * θ ^ θ
      = (Avol ^ ninv) ^ (1 - θ) * (Bvol ^ ninv) ^ θ
        / (Avol ^ ninv + Bvol ^ ninv) := by
    conv_lhs =>
      congr
      · congr; rw [hone_minus_θ]
    rw [Real.div_rpow, Real.div_rpow, ← mul_div_mul_comm,
      ← Real.rpow_add, sub_add_cancel, Real.rpow_one]
    iterate 5 positivity

  rw [this] at prekopa_leindler_special_case_θ

  conv_rhs at prekopa_leindler_special_case_θ =>
    rw [div_pow, mul_pow,
      ← Real.rpow_mul (by positivity),
      ← Real.rpow_mul_natCast (by positivity),
      ← Real.rpow_mul (by positivity),
      ← Real.rpow_mul_natCast (by positivity)]
    conv in (occs := 1 2) (ninv * _ * (n : ℝ)) =>
      all_goals rw [mul_comm, ← mul_assoc,
        mul_inv_cancel₀ (Nat.cast_ne_zero.mpr ngz), one_mul]

  rw [div_mul_eq_mul_div₀, le_div_iff₀ (by positivity),
    mul_le_mul_left (by positivity)] at prekopa_leindler_special_case_θ

  -- Modify the goal
  apply le_of_pow_le_pow_left₀ ngz (by positivity)
  rwa [← NNReal.rpow_mul_natCast, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr ngz),
    NNReal.rpow_one]
