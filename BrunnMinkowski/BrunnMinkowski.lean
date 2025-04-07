import Mathlib.Analysis.Convex.Body
import BrunnMinkowski.PrekopaLeindlerCombine

open Set MeasureTheory ENNReal
open scoped Pointwise NNReal

variable {I : Type} [Fintype I] {n : ℕ}

noncomputable def ConvexBody.volume (A : ConvexBody (ℝI I)) : NNReal :=
  (MeasureTheory.volume (A : Set (ℝI I))).toNNReal


lemma Rn_volume_le_volume_add_right {A B : Set (ℝn n)} (hB : B.Nonempty) :
    volume A ≤ volume (A + B) := by
  obtain ⟨b, hb⟩ := hB
  calc
    volume A
      = volume (A + {b}) := by
      rw [add_singleton, image_add_right, measure_preimage_add_right]
    _ ≤ volume (A + B) := by
      refine measure_mono (add_subset_add_left ?_)
      exact singleton_subset_iff.mpr hb

lemma Rn_volume_le_volume_add_left {A B : Set (ℝn n)} (hB : B.Nonempty) :
    volume A ≤ volume (B + A) := by
  rw [add_comm]
  exact Rn_volume_le_volume_add_right hB

lemma pos_rpow_of_pos {x : ℝ≥0∞} {r : ℝ} (hx : x ≠ 0) (hr : 0 < r) :
    0 < x ^ r := by
  rw [← zero_rpow_of_pos hr, rpow_lt_rpow_iff hr]
  positivity


-- Brunn--Minkowski inequality for measurable sets of finite measure
theorem brunn_minkowski_fin_meas
    (hn_nonzero : n ≠ 0)
    {A B : Set (ℝn n)}
    (hA_nonempty : A.Nonempty) (hA_meas : MeasurableSet A) (hAvol_fin : volume A ≠ ⊤)
    (hB_nonempty : B.Nonempty) (hB_meas : MeasurableSet B) (hBvol_fin : volume B ≠ ⊤)
    (hAB_meas : MeasurableSet (A + B)) :
    volume A ^ (n⁻¹ : ℝ) + volume B ^ (n⁻¹ : ℝ)
      ≤ volume (A + B) ^ (n⁻¹ : ℝ) := by

  let ninv := (n⁻¹ : ℝ)
  let volA := volume A
  let volB := volume B

  change volA ≠ ⊤ at hAvol_fin; change volB ≠ ⊤ at hBvol_fin

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
  have Avol_pow_ninv_ne_top := rpow_of_ninv_ne_top hAvol_fin
  have Bvol_pow_ninv_ne_top := rpow_of_ninv_ne_top hBvol_fin


  rcases eq_zero_or_pos (volume A) with hAvol | hAvol_pos
  · -- Assume volume A = 0
    rw [hAvol, zero_rpow_of_ninv, zero_add, rpow_of_ninv_le_iff]
    exact Rn_volume_le_volume_add_left hA_nonempty
  rcases eq_zero_or_pos (volume B) with hBvol | hBvol_pos
  · -- Assume volume B = 0
    rw [hBvol, zero_rpow_of_ninv, add_zero, rpow_of_ninv_le_iff]
    exact Rn_volume_le_volume_add_right hB_nonempty
  rcases eq_or_ne (volume (A + B)) ⊤ with hABvol | hABvol_fin
  · -- Assume volume (A + B) = ⊤
    rw [hABvol, top_rpow_of_pos ninv_pos]
    exact le_top


  change 0 < volA at hAvol_pos; change 0 < volB at hBvol_pos

  -- volA ^ ninv, volB ^ ninv ≠ 0
  have Avol_pow_ninv_pos : 0 < volA ^ ninv := pos_rpow_of_pos (ne_of_gt hAvol_pos) ninv_pos
  have Bvol_pow_ninv_pos : 0 < volB ^ ninv := pos_rpow_of_pos (ne_of_gt hBvol_pos) ninv_pos


  have prekopa_leindler_special_case
      {t : ℝ} (h0t : 0 < t) (ht1 : t < 1) :
      (volume A) ^ (1 - t) * (volume B) ^ t
        ≤ (ENNReal.ofReal ((1 - t) ^ (1 - t) * t ^ t) ^ n) * (volume (A + B)) := by

    have t_nonneg : 0 ≤ t := le_of_lt h0t
    have hone_sub_t_pos : 0 < 1 - t := sub_pos.mpr ht1
    have hone_sub_t_nonneg : 0 ≤ 1 - t := le_of_lt hone_sub_t_pos
    have t_pow_nonneg : 0 ≤ t ^ t := Real.rpow_nonneg t_nonneg t
    have one_sub_t_pow_nonneg : 0 ≤ (1 - t) ^ (1 - t) :=
      Real.rpow_nonneg hone_sub_t_nonneg (1 - t)

    -- Define the indicator functions on A, B, and A + B
    let ind_A : (ℝn n) → ℝ := indicator A 1
    let ind_B : (ℝn n) → ℝ := indicator B 1
    let ind_AB : (ℝn n) → ℝ := indicator (A + B) 1

    -- Check the indicator functions satisfy the condition of Prékopa-Leindler
    have hind_cond (x y : ℝn n) :
        (ind_A x) ^ (1 - t) * (ind_B y) ^ t ≤ ind_AB (x + y) := by
      by_cases hx_nmem_A : x ∉ A
      · -- Assume x ∉ A
        simp only [ind_A, ind_AB,
          indicator_of_not_mem hx_nmem_A,
          Real.zero_rpow (ne_of_gt hone_sub_t_pos), zero_mul,
          indicator_apply_nonneg, Pi.one_apply, zero_le_one, implies_true]
      by_cases hy_nmem_B : y ∉ B
      · -- Assume y ∉ B
        simp only [ind_B, ind_AB,
          indicator_of_not_mem hy_nmem_B,
          Real.zero_rpow (ne_of_gt h0t), mul_zero,
          indicator_apply_nonneg, Pi.one_apply, zero_le_one, implies_true]

      have hx_mem_A : x ∈ A := of_not_not hx_nmem_A
      have hy_mem_B : y ∈ B := of_not_not hy_nmem_B
      have hxy_mem_AB : x + y ∈ A + B :=  mem_add.mpr ⟨x, hx_mem_A, y, hy_mem_B, rfl⟩

      unfold ind_A ind_B ind_AB
      rw [indicator_of_mem hx_mem_A, indicator_of_mem hy_mem_B,
        indicator_of_mem hxy_mem_AB]
      norm_num

    -- Apply Prékopa-Leindler
    have prekopa_leinler_app :
      (∫ x, ind_A x) ^ (1 - t) * (∫ y, ind_B y) ^ t ≤
        (1 - t) ^ (n * (1 - t)) * t ^ (n * t) * (∫ x, ind_AB x) := by
      refine prekopa_leindler h0t ht1 ?_ ?_ ?_ ?_ ?_ ?_ hind_cond
      · -- 0 ≤ ind_A
        exact indicator_nonneg (fun _ _ ↦ (by norm_num))
      · -- Integrable ind_A
        refine IntegrableOn.integrable_indicator ?_ hA_meas
        exact integrableOn_const.mpr (Or.inr hAvol_fin.lt_top)
      · -- 0 ≤ ind_B
        exact indicator_nonneg (fun _ _ ↦ (by norm_num))
      · -- Integrable ind_B
        refine IntegrableOn.integrable_indicator ?_ hB_meas
        exact integrableOn_const.mpr (Or.inr hBvol_fin.lt_top)
      · -- 0 ≤ ind_AB
        exact indicator_nonneg (fun _ _ ↦ (by norm_num))
      · -- Integrable ind_AB
        refine IntegrableOn.integrable_indicator ?_ hAB_meas
        exact integrableOn_const.mpr (Or.inr hABvol_fin.lt_top)

    -- Modify the special case of Prékopa–Leindler
    unfold ind_A ind_B ind_AB at prekopa_leinler_app
    rw [integral_indicator_one hA_meas,
      integral_indicator_one hB_meas,
      integral_indicator_one hAB_meas] at prekopa_leinler_app

    apply ofReal_le_ofReal at prekopa_leinler_app
    conv at prekopa_leinler_app =>
      rw [ofReal_mul (Real.rpow_nonneg toReal_nonneg (1 - t)),
        ofReal_mul' (toReal_nonneg)]
      rw [← ofReal_rpow_of_pos (toReal_pos (ne_of_gt hAvol_pos) hAvol_fin),
        ← ofReal_rpow_of_pos (toReal_pos (ne_of_gt hBvol_pos) hBvol_fin),
        ofReal_toReal_eq_iff.mpr hAvol_fin,
        ofReal_toReal_eq_iff.mpr hBvol_fin,
        ofReal_toReal_eq_iff.mpr hABvol_fin]
      conv in (occs := *) ((n : ℝ) * _) => all_goals rw [mul_comm]
      rw [Real.rpow_mul hone_sub_t_nonneg,
        Real.rpow_mul t_nonneg]
      rw [← Real.mul_rpow one_sub_t_pow_nonneg t_pow_nonneg]

    rwa [← ofReal_pow (mul_nonneg one_sub_t_pow_nonneg t_pow_nonneg) n,
      ← Real.rpow_natCast]


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
      ofReal_div_of_pos (toReal_pos denom_nonzero denom_ne_top),
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
    · exact pos_rpow_of_pos (ne_of_gt hAvol_pos) hone_sub_θ_pos
    · exact pos_rpow_of_pos (ne_of_gt hBvol_pos) hθ.1
  case h2 =>
    refine mul_ne_top ?_ ?_
    · exact rpow_ne_top_of_nonneg (le_of_lt hone_sub_θ_pos) hAvol_fin
    · exact rpow_ne_top_of_nonneg (le_of_lt hθ.1) hBvol_fin

  apply ENNReal.mul_le_of_le_div at prekopa_leindler_special_case_θ
  rw [one_mul] at prekopa_leindler_special_case_θ

  rwa [← ENNReal.rpow_le_rpow_iff n_toreal_pos,
    ← ENNReal.rpow_mul,
    inv_mul_cancel₀ (ne_of_gt n_toreal_pos), rpow_one]


-- Brunn--Minkowski inequality for measurable sets
theorem brunn_minkowski_measurable
    (hn_nonzero : n ≠ 0)
    {A B : Set (ℝn n)}
    (hA_nonempty : A.Nonempty) (hA_meas : MeasurableSet A)
    (hB_nonempty : B.Nonempty) (hB_meas : MeasurableSet B)
    (hAB_meas : MeasurableSet (A + B)) :
    volume A ^ (n⁻¹ : ℝ) + volume B ^ (n⁻¹ : ℝ)
      ≤ volume (A + B) ^ (n⁻¹ : ℝ) := by

  have ninv_pos : 0 < (n⁻¹ : ℝ) := by
    simp only [inv_pos, Nat.cast_pos, Nat.pos_of_ne_zero hn_nonzero]

  rcases eq_or_ne (volume (A + B)) ⊤ with hABvol | hABvol_fin
  · -- Assume volume (A + B) = ⊤
    rw [hABvol, top_rpow_of_pos ninv_pos]
    exact le_top

  have hAvol_fin : volume A ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt (Rn_volume_le_volume_add_right hB_nonempty)
      hABvol_fin.lt_top
  have hBvol_fin : volume B ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt (Rn_volume_le_volume_add_left hA_nonempty)
      hABvol_fin.lt_top

  exact brunn_minkowski_fin_meas hn_nonzero
    hA_nonempty hA_meas hAvol_fin
    hB_nonempty hB_meas hBvol_fin
    hAB_meas


-- Brunn-Minkowski inequality for convex bodies
theorem brunn_minkowski_convex_bodies
    (hn_nonzero : n ≠ 0)
    (A B : ConvexBody (ℝn n)) :
    A.volume ^ (n⁻¹ : ℝ) + B.volume ^ (n⁻¹ : ℝ)
      ≤ (A + B).volume ^ (n⁻¹ : ℝ) := by

  have ninv_nonneg : 0 ≤ (n⁻¹ : ℝ) := inv_nonneg.mpr (Nat.cast_nonneg n)

  have Avol_fin : volume (A : (Set (ℝn n))) ≠ ⊤ :=
    ne_of_lt (IsCompact.measure_lt_top A.isCompact)
  have Bvol_fin : volume (B : (Set (ℝn n))) ≠ ⊤ :=
    ne_of_lt (IsCompact.measure_lt_top B.isCompact)
  have ABvol_fin : volume (A + B : (Set (ℝn n))) ≠ ⊤ :=
    ne_of_lt (IsCompact.measure_lt_top (IsCompact.add A.isCompact B.isCompact))

  unfold ConvexBody.volume
  iterate 3 rw [← toNNReal_rpow]
  rw [← toNNReal_add
      (rpow_ne_top_of_nonneg ninv_nonneg Avol_fin)
      (rpow_ne_top_of_nonneg ninv_nonneg Bvol_fin)]
  apply toNNReal_mono (rpow_ne_top_of_nonneg ninv_nonneg ABvol_fin)

  exact brunn_minkowski_measurable hn_nonzero
    (ConvexBody.nonempty A)
    (IsCompact.measurableSet (A.isCompact))
    (ConvexBody.nonempty B)
    (IsCompact.measurableSet (B.isCompact))
    (IsCompact.measurableSet (IsCompact.add A.isCompact B.isCompact))
