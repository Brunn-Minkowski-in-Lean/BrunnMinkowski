import Mathlib.Analysis.Convex.Body
import BrunnMinkowski.PrekopaLeindler

open Set MeasureTheory ENNReal
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
      refine ENNReal.toNNReal_mono (convbody_set_vol_ne_top (A + B))
        (MeasureTheory.measure_mono (Set.add_subset_add_left ?_))
      simp only [singleton_to_convbody, ConvexBody.coe_mk,
        Set.singleton_subset_iff, hb]


lemma Rn_volume_le_volume_add_right
    {A B : Set (ℝn n)} (hB : Nonempty B) :
    volume A ≤ volume (A + B) := by
  obtain ⟨b, hb⟩ := hB
  calc
    volume A = volume (A + {b}) := by
      rw [add_singleton, image_add_right, measure_preimage_add_right]
    _ ≤ volume (A + B) := by
      refine measure_mono (add_subset_add_left ?_)
      exact singleton_subset_iff.mpr hb

lemma pos_rpow_of_pos {x : ℝ≥0∞} {r : ℝ} (hx : x ≠ 0) (hr : 0 < r) :
    0 < x ^ r := by
  rw [← zero_rpow_of_pos hr, rpow_lt_rpow_iff hr]
  positivity


-- Brunn--Minkowski inequality for finite measure sets
theorem brunn_minkowski_fin_meas
    {hn_nonzero : n ≠ 0}
    {A B : Set (ℝn n)}
    (hA_nonempty : Nonempty A) (hA_fin_vol : volume A ≠ ⊤)
    (hB_nonempty : Nonempty B) (hB_fin_vol : volume B ≠ ⊤) :
    volume A ^ (n⁻¹ : ℝ) + volume B ^ (n⁻¹ : ℝ)
      ≤ volume (A + B) ^ (n⁻¹ : ℝ) := by

  let ninv := (n⁻¹ : ℝ)
  let volA := volume A
  let volB := volume B
  -- let volAB := volume (A + B)

  change volA ≠ ⊤ at hA_fin_vol; change volB ≠ ⊤ at hB_fin_vol

  have ninv_pos : 0 < ninv := by
    simp only [ninv, inv_pos, Nat.cast_pos, Nat.pos_of_ne_zero hn_nonzero]
  have n_toreal_pos : 0 < (n : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn_nonzero)
  have zero_rpow_of_ninv : (0 : ℝ≥0∞) ^ ninv = 0 := zero_rpow_of_pos ninv_pos
  have rpow_of_ninv_le_iff {x y : ℝ≥0∞} : x ^ ninv ≤ y ^ ninv ↔ x ≤ y :=
    rpow_le_rpow_iff ninv_pos
  have rpow_of_ninv_lt_iff {x y : ℝ≥0∞} : x ^ ninv < y ^ ninv ↔ x < y :=
    rpow_lt_rpow_iff ninv_pos


  -- volA ^ ninv, volB ^ ninv ≠ ⊤
  have rpow_of_ninv_ne_top {x : ℝ≥0∞} (hx : x ≠ ⊤) : x ^ ninv ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (le_of_lt ninv_pos) hx
  have Avol_pow_ninv_ne_top := rpow_of_ninv_ne_top hA_fin_vol
  have Bvol_pow_ninv_ne_top := rpow_of_ninv_ne_top hB_fin_vol


  rcases eq_zero_or_pos (volume A) with hAvol | hAvol
  · -- Assume volume A = 0
    rw [hAvol, zero_rpow_of_ninv, zero_add, rpow_of_ninv_le_iff, add_comm]
    exact Rn_volume_le_volume_add_right hA_nonempty
  rcases eq_zero_or_pos (volume B) with hBvol | hBvol
  · -- Assume volume B = 0
    rw [hBvol, zero_rpow_of_ninv, add_zero, rpow_of_ninv_le_iff]
    exact Rn_volume_le_volume_add_right hB_nonempty

  change 0 < volA at hAvol; change 0 < volB at hBvol

  -- volA ^ ninv, volB ^ ninv ≠ 0
  have Avol_pow_ninv_pos : 0 < volA ^ ninv := pos_rpow_of_pos (ne_of_gt hAvol) ninv_pos
  have Bvol_pow_ninv_pos : 0 < volB ^ ninv := pos_rpow_of_pos (ne_of_gt hBvol) ninv_pos


  have prekopa_leindler_special_case
      {t : ℝ} (h0t : 0 < t) (ht1 : t < 1) :
      (volume A) ^ (1 - t) * (volume B) ^ t
        ≤ (ENNReal.ofReal ((1 - t) ^ (1 - t) * t ^ t) ^ n) * (volume (A + B)) := by
    sorry


  -- Use θ as an input in t
  let θ : ℝ := (volB ^ ninv / (volA ^ ninv + volB ^ ninv)).toReal

  have denom_pos : 0 < volA ^ ninv + volB ^ ninv :=
    add_pos_of_pos_of_nonneg Avol_pow_ninv_pos (le_of_lt Bvol_pow_ninv_pos)

  have denom_nonzero : volA ^ ninv + volB ^ ninv ≠ 0 := ne_of_gt denom_pos

  have denom_ne_top : volA ^ ninv + volB ^ ninv ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨Avol_pow_ninv_ne_top, Bvol_pow_ninv_ne_top⟩

  have hone_sub_θ : 1 - θ = (volA ^ ninv / (volA ^ ninv + volB ^ ninv)).toReal := by
    have := ENNReal.toReal_ne_zero.mpr ⟨denom_nonzero, denom_ne_top⟩
    unfold θ
    rw [toReal_div, toReal_div, eq_div_iff this,
      sub_mul, div_mul_cancel₀ _ this, one_mul, sub_eq_of_eq_add]
    exact ENNReal.toReal_add Avol_pow_ninv_ne_top Bvol_pow_ninv_ne_top

  have hθ : 0 < θ ∧ θ < 1 := by
    constructor
    · -- 0 < θ
      rw [toReal_pos_iff, ENNReal.div_pos_iff]
      constructor
      · exact ⟨(ne_of_gt Bvol_pow_ninv_pos), denom_ne_top⟩
      · exact div_lt_top Bvol_pow_ninv_ne_top denom_nonzero
    · -- θ < 1
      refine toReal_lt_of_lt_ofReal (div_lt_of_lt_mul ?_)
      simp only [ofReal_one, one_mul]
      rw [add_comm]
      exact lt_add_right Bvol_pow_ninv_ne_top (ne_of_gt Avol_pow_ninv_pos)

  have hone_sub_θ_pos : 0 < 1 - θ := by simp only [sub_pos, hθ.2]

  -- Modify the special case of Prékopa–Leindler with t = θ
  have prekopa_leindler_special_case_θ := prekopa_leindler_special_case hθ.1 hθ.2

  have : ENNReal.ofReal ((1 - θ) ^ (1 - θ) * θ ^ θ)
      = (volA ^ ninv) ^ (1 - θ) * (volB ^ ninv) ^ θ
          / (volA ^ ninv + volB ^ ninv) := by
    rw [ENNReal.ofReal_mul' (Real.rpow_nonneg (le_of_lt hθ.1) θ)]
    rw [← ENNReal.ofReal_rpow_of_pos hone_sub_θ_pos,
      ← ENNReal.ofReal_rpow_of_pos hθ.1]
    conv_lhs => enter [1, 1, 1]; rw [hone_sub_θ]
    conv_lhs => enter [2, 1]; unfold θ
    iterate 2 rw [toReal_div,
      ofReal_div_of_pos
        (toReal_pos denom_nonzero denom_ne_top),
      ofReal_toReal denom_ne_top]
    rw [ofReal_toReal Avol_pow_ninv_ne_top,
      ofReal_toReal Bvol_pow_ninv_ne_top]
    rw [div_rpow_of_nonneg _ _ (le_of_lt hone_sub_θ_pos),
      div_rpow_of_nonneg _ _ (le_of_lt hθ.1)]
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
    conv_lhs => enter [2]; rw [mul_left_comm]
    rw [← mul_assoc, ← ENNReal.mul_inv ?ha ?hb]
    case ha =>
      left; exact ne_of_gt (pos_rpow_of_pos denom_nonzero hone_sub_θ_pos)
    case hb =>
      right; exact ne_of_gt (pos_rpow_of_pos denom_nonzero hθ.1)
    rw [← div_eq_mul_inv, ← ENNReal.rpow_add _ _ denom_nonzero denom_ne_top,
      sub_add_cancel, rpow_one]

  rw [this] at prekopa_leindler_special_case_θ

  unfold volA volB at prekopa_leindler_special_case_θ

  conv_rhs at prekopa_leindler_special_case_θ =>
    rw [← ENNReal.rpow_natCast]
    rw [div_rpow_of_nonneg _ _ (Nat.cast_nonneg n)]
    rw [mul_rpow_of_nonneg _ _ (Nat.cast_nonneg n)]
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    conv in (occs := *) (ninv * (_ * (n : ℝ))) =>
      all_goals
        rw [mul_comm, mul_assoc,
          mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn_nonzero), mul_one]

  apply Eq.trans_le (mul_one _) at prekopa_leindler_special_case_θ

  rw [ENNReal.mul_comm_div, mul_le_mul_left ?h1 ?h2]
    at prekopa_leindler_special_case_θ
  case h1 =>
    refine ne_of_gt (mul_pos (ne_of_gt ?_) (ne_of_gt ?_))
    · exact pos_rpow_of_pos (ne_of_gt hAvol) hone_sub_θ_pos
    · exact pos_rpow_of_pos (ne_of_gt hBvol) hθ.1
  case h2 =>
    refine mul_ne_top ?_ ?_
    · exact rpow_ne_top_of_nonneg (le_of_lt hone_sub_θ_pos) hA_fin_vol
    · exact rpow_ne_top_of_nonneg (le_of_lt hθ.1) hB_fin_vol

  apply ENNReal.mul_le_of_le_div at prekopa_leindler_special_case_θ
  rw [one_mul] at prekopa_leindler_special_case_θ

  rwa [← ENNReal.rpow_le_rpow_iff n_toreal_pos,
    ← ENNReal.rpow_mul,
    inv_mul_cancel₀ (ne_of_gt n_toreal_pos), rpow_one]


-- Brunn-Minkowski inequality for convex bodies
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

  have prekopa_leindler_special_case {t : ℝ} (h0t : 0 < t) (ht1 : t < 1) :
      Avol ^ (1 - t) * Bvol ^ t
      ≤ ((1 - t) ^ (1 - t) * t ^ t) ^ n * (A + B).volume := by

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

    -- Apply Prékopa-Leindler
    have prekopa_leinler_app :
      (∫ x, ind_A x) ^ (1 - t) * (∫ y, ind_B y) ^ t ≤
        (1 - t)^(n * (1-t)) * t ^ (n * t) * (∫ x, ind_ABsum x) := by
      refine prekopa_leindler h0t ht1
        ind_A ind_B ind_ABsum
        ?_ ?_ ?_ ?_ ?_ ?_
        hind_cond
      · intro a
        refine Set.indicator_apply_nonneg ?_
        intro; simp only [Pi.one_apply, zero_le_one]
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry

    -- ∫ indicator function of C = C.volume
    have hind_ConvBody_int_eq_vol
        (C : ConvexBody (ℝn n)) {f : (ℝn n) → ℝ}
        (hf : f = (C : Set (ℝn n)).indicator 1) :
        ∫ x, f x = C.volume := by
      rw [hf, MeasureTheory.integral_indicator_one]
      simp only [hf, MeasureTheory.integral_indicator_one,
        ConvexBody.volume, ENNReal.coe_toNNReal_eq_toReal]
      exact IsCompact.measurableSet C.isCompact

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

  sorry

  rw [div_mul_eq_mul_div₀, le_div_iff₀ (by positivity),
    mul_le_mul_left (by positivity)] at prekopa_leindler_special_case_θ

  -- Modify the goal
  apply le_of_pow_le_pow_left₀ ngz (by positivity)
  rwa [← NNReal.rpow_mul_natCast, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr ngz),
    NNReal.rpow_one]
