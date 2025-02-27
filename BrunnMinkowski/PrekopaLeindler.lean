import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

import BrunnMinkowski.MeasureTheoryLemmas
import BrunnMinkowski.EuclideanSpace
import BrunnMinkowski.OneDim

open NNReal ENNReal MeasureTheory Finset
open Real Set MeasureTheory Filter Asymptotics

open scoped Real Topology

open Pointwise

-- isomorhpism from any f.d. R-v.s. to R^d
-- #check toEuclidean

theorem EuclideanSpace.induction_on_dimension
    {P : (α : Type) →
      [AddCommGroup α] → [TopologicalSpace α] →  [TopologicalAddGroup α] → [T2Space α] → [Module ℝ α] → [ContinuousSMul ℝ α] → [FiniteDimensional ℝ α] → Sort}
    {base0 : P (EuclideanSpace ℝ (Fin 0))}
    {base1 : P ℝ}
    {induct : {α β : Type} →
      [AddCommGroup α] → [TopologicalSpace α] →  [TopologicalAddGroup α] → [T2Space α] → [Module ℝ α] → [ContinuousSMul ℝ α] → [FiniteDimensional ℝ α] →
      [AddCommGroup β] → [TopologicalSpace β] →  [TopologicalAddGroup β] → [T2Space β] → [Module ℝ β] → [ContinuousSMul ℝ β] → [FiniteDimensional ℝ β] →
      P α → P β → P (α × β)} :
  (α : Type) → [AddCommGroup α] → [TopologicalSpace α] →  [TopologicalAddGroup α] → [T2Space α] → [Module ℝ α] → [ContinuousSMul ℝ α] → [FiniteDimensional ℝ α] → P α := by sorry


lemma one_dim_BMInequality_of_nullmeasurable (A B C : Set ℝ)
    (hA_nonempty : A.Nonempty) (hB_nonempty : B.Nonempty)
    (hA_nm : NullMeasurableSet A)
    (hB_nm : NullMeasurableSet B)
    (hABC : A + B ⊆ C)
    : volume A + volume B ≤ volume C := by

  obtain ⟨Am, hAm_subset_A, hAm_m, hAm_ae_eq⟩ :=
    NullMeasurableSet.exists_measurable_subset_ae_eq hA_nm
  obtain ⟨Bm, hBm_subset_B, hBm_m, hBm_ae_eq⟩ :=
    NullMeasurableSet.exists_measurable_subset_ae_eq hB_nm
  let Cm := toMeasurable volume C

  have hAm_vol_eq := measure_congr hAm_ae_eq
  have hBm_vol_eq := measure_congr hBm_ae_eq

  have hAvol_nonneg := le_iff_eq_or_lt.1 (Measure.zero_le volume A)
  have hBvol_nonneg := le_iff_eq_or_lt.1 (Measure.zero_le volume B)
  simp only [Measure.coe_zero, Pi.zero_apply] at hAvol_nonneg hBvol_nonneg

  rcases eq_or_ne (volume A) 0 with hA_vol_zero | hA_vol_nonzero
  · -- Assume volume A = 0
    rw [hA_vol_zero, zero_add]
    calc
      volume B
      _ ≤ volume (A + B) := volume_le_volume_add_left hA_nonempty
      _ ≤ volume C := measure_mono hABC
  rcases eq_or_ne (volume B) 0 with hB_vol_zero | hB_vol_nonzero
  · -- Assume volume B = 0
    rw [hB_vol_zero, add_zero]
    calc
      volume A
      _ ≤ volume (A + B) := volume_le_volume_add_right hB_nonempty
      _ ≤ volume C := measure_mono hABC

  have AmBmCm : Am + Bm ⊆ Cm :=
    calc
      Am + Bm
        ⊆ A + B := Set.add_subset_add hAm_subset_A hBm_subset_B
      _ ⊆ C := hABC
      _ ⊆ Cm := subset_toMeasurable volume C

  have Am_nonempty :=
    nonempty_of_measure_ne_zero (Eq.trans_ne hAm_vol_eq hA_vol_nonzero)
  have Bm_nonempty :=
    nonempty_of_measure_ne_zero (Eq.trans_ne hBm_vol_eq hB_vol_nonzero)

  have hAmBmCm_vol : volume Am + volume Bm ≤ volume Cm := by
    refine one_dim_BMInequality Am Bm Cm
      Am_nonempty Bm_nonempty ?_
      hAm_m hBm_m (measurableSet_toMeasurable volume C)
      AmBmCm
    · exact Set.Nonempty.mono AmBmCm (Set.Nonempty.add Am_nonempty Bm_nonempty)

  rw [hAm_vol_eq, hBm_vol_eq, measure_toMeasurable C] at hAmBmCm_vol
  exact hAmBmCm_vol

lemma nonneg_integrable_integral_eq_integral_superlevel_set_meas
    {f : ℝn n → ℝ} (hf_nonneg : 0 ≤ f) (hf_integrable : Integrable f) :
    (∫ x, f x) = (∫ y, (fun l ↦ (volume (superlevel_set f l)).toReal) y) := by
  sorry



theorem prekopa_leindler
    {t : ℝ} (h0t : 0 < t) (ht1 : t < 1)
    {d : ℕ} (f g h : ℝn d → ℝ)
    (hf_nonneg : 0 ≤ f) (hf_integrable : Integrable f)
    (hf_nonneg : 0 ≤ g) (hg_integrable : Integrable g)
    (hf_nonneg : 0 ≤ h) (hh_integrable : Integrable h)
    (hfgh_pow_le :
      ∀ x y : ℝn d,
      (f x)^(1 - t) * (g y)^t ≤ h (x + y)) :
  (∫ x, f x)^(1-t) * (∫ y, g y)^t ≤
  (1 - t)^(d * (1-t)) * t^(d*t) * (∫ x, h x)
  := by sorry


-- write claims in the form of lemmas
-- show that if PL holds for a fixed f and any essentially bounded g,
-- then it holds for f and every g

lemma prekopa_leindler_dim1
    {t : ℝ} (h0t : 0 < t) (ht1 : t < 1)
    {f g h : ℝn 1 → ℝ}
    (hf_nonneg : 0 ≤ f) (hf_integrable : Integrable f)
    (hg_nonneg : 0 ≤ g) (hg_integrable : Integrable g)
    (hh_nonneg : 0 ≤ h) (hh_integrable : Integrable h)
    (hfgh_pow_le : ∀ x y : ℝn 1,
      (f x) ^ (1 - t) * (g y) ^ t ≤ h (x + y)) :
    (∫ x, f x) ^ (1 - t) * (∫ y, g y) ^ t
      ≤ (1 - t) ^ (1 - t) * t ^ t * (∫ x, h x) := by

  -- abbreviations
  let prekopa_leindler_dim1_conclusion :=
    (∫ x, f x) ^ (1 - t) * (∫ y, g y) ^ t
      ≤ (1 - t) ^ (1 - t) * t ^ t * (∫ x, h x)

  let f_essBdd := IsEssBdd f volume
  let g_essBdd := IsEssBdd g volume

  -- conditions on t
  have one_sub_t_pos : 0 < 1 - t := sub_pos.mpr ht1
  have t_nonneg : 0 ≤ t := le_of_lt h0t

  -- essential supremums
  let f_essSup : ℝ := essSup f volume
  let g_essSup : ℝ := essSup g volume
  let h_essSup : ℝ := essSup h volume

  have f_essSup_nonneg : 0 ≤ f_essSup := nonneg_essSup_of_nonneg hf_nonneg
  have g_essSup_nonneg : 0 ≤ g_essSup := nonneg_essSup_of_nonneg hg_nonneg
  have h_essSup_nonneg : 0 ≤ h_essSup := nonneg_essSup_of_nonneg hh_nonneg

  have superlevel_sets_subset {f g h : ℝn 1 → ℝ}
      {l : ℝ} (hl_pos : 0 < l)
      (hfgh_pow_le : ∀ x y : ℝn 1,
        (f x) ^ (1 - t) * (g y) ^ t ≤ h (x + y)) :
      superlevel_set f l + superlevel_set g l ⊆ superlevel_set h l := by
    refine Set.add_subset_iff.mpr ?_
    intro x hx y hy
    rw [superlevel_set, mem_setOf_eq] at *
    calc
      l = l ^ (1 - t) * l ^ t := by
        rw [← rpow_add hl_pos, sub_add_cancel, rpow_one l]
      _ < (f x) ^ (1 - t) * (g y) ^ t := by gcongr
      _ ≤ h (x + y) := by exact hfgh_pow_le x y

  -- The conclusion holds when f or g is a.e. zero
  by_cases hf_ae_zero : f =ᵐ[volume] 0
  · -- Assume f is a.e. zero
    have : (∫ x, f x) = 0 := integral_eq_zero_of_ae hf_ae_zero
    rw [this, Real.zero_rpow (by positivity), zero_mul]
    exact mul_nonneg (by positivity) (integral_nonneg hh_nonneg)
  by_cases hg_ae_zero : g =ᵐ[volume] 0
  · -- Assume g is a.e. zero
    have : (∫ x, g x) = 0 := integral_eq_zero_of_ae hg_ae_zero
    rw [this, Real.zero_rpow (by positivity), mul_zero]
    exact mul_nonneg (by positivity) (integral_nonneg hh_nonneg)

  have hf_not_ae_zero := ne_eq hf_ae_zero
  have hg_not_ae_zero := ne_eq hg_ae_zero

  -- (∫ x, f x) + (∫ x, g x) ≤ (∫ x, h x) holds if f and g are essentially bounded and not a.e. zero
  have integral_sum_le_of_essBdd_essSup_nonzero
      (hf_essBdd : IsEssBdd f) (hg_essBdd : IsEssBdd g)
      : (∫ x, f x) + (∫ x, g x) ≤ (∫ x, h x) := by

    have f_essSup_pos : 0 < f_essSup := by
      by_contra hf_essSup_zero
      apply eq_of_ge_of_not_gt f_essSup_nonneg at hf_essSup_zero
      have := ae_zero_of_nonneg_essSup_zero_essBdd
        hf_nonneg hf_essBdd hf_essSup_zero
      contradiction
    have g_essSup_pos : 0 < g_essSup := by
      by_contra hg_essSup_zero
      apply eq_of_ge_of_not_gt g_essSup_nonneg at hg_essSup_zero
      have := ae_zero_of_nonneg_essSup_zero_essBdd
        hg_nonneg hg_essBdd hg_essSup_zero
      contradiction

    -- normalize the essential supremums
    let f_nor : ℝn 1 → ℝ := fun x ↦ (f x) / f_essSup
    let g_nor : ℝn 1 → ℝ := fun x ↦ (g x) / g_essSup
    let h_nor : ℝn 1 → ℝ := fun x ↦ (h x) / (f_essSup ^ (1 - t) * g_essSup ^ t)

    have f_nor_nonneg : 0 ≤ f_nor := by
      intro; exact div_nonneg (hf_nonneg _) f_essSup_nonneg
    have g_nor_nonneg : 0 ≤ g_nor := by
      intro; exact div_nonneg (hg_nonneg _) g_essSup_nonneg

    have f_nor_essSup_eq_one : essSup f_nor volume = 1 := by
      rw [← div_self (ne_of_gt f_essSup_pos)]
      have  (x : ℝn 1) : 0 ≤ f x := hf_nonneg x
      exact div_essSup_of_essBdd_lowerBdd _ hf_essBdd this f_essSup_pos
    have g_nor_essSup_eq_one : essSup g_nor volume = 1 := by
      rw [← div_self (ne_of_gt g_essSup_pos)]
      have (x : ℝn 1) : 0 ≤ g x := hg_nonneg x
      exact div_essSup_of_essBdd_lowerBdd _ hg_essBdd this g_essSup_pos

    have nor_superlevel_sets_subset {l : ℝ} (hl_pos : 0 < l) :
        superlevel_set f_nor l + superlevel_set g_nor l ⊆ superlevel_set h_nor l
        := by
      refine superlevel_sets_subset hl_pos ?_
      unfold f_nor g_nor h_nor
      intro x y
      rw [Real.div_rpow (hf_nonneg x) f_essSup_nonneg,
        Real.div_rpow (hg_nonneg y) g_essSup_nonneg,
        div_mul_div_comm]
      gcongr
      exact hfgh_pow_le x y

    have {l : ℝ} (h0l : 0 < l) (hl1 : l < 1) :
        volume (superlevel_set f_nor l) + volume (superlevel_set g_nor l)
          ≤ volume (superlevel_set h_nor l) := by

      let ϕ : ℝ ≃ᵐ ℝn 1 := (MeasurableEquiv.funUnique (Fin 1) ℝ).symm
      let A : Set ℝ := ϕ ⁻¹' (superlevel_set f_nor l)
      let B : Set ℝ := ϕ ⁻¹' (superlevel_set g_nor l)
      let C : Set ℝ := ϕ ⁻¹' (superlevel_set h_nor l)
      -- use NullMeasurableSet.exists_measurable_subset_ae_eq and nullmeasurable_superlevel_set_of_aemeasurable to make measurable sets
      -- Measurable.nullMeasurable


      have ϕ_preserves_volume {D : Set (ℝn 1)} :
          volume (ϕ ⁻¹' D) = volume D := by
        -- MeasureTheory.volume_preserving_funUnique?
        -- MeasurableEquiv.funUnique?
        sorry

      have ϕ_preimage_nonempty {D : Set (ℝn 1)} (hD : D.Nonempty) :
          (ϕ ⁻¹' (D)).Nonempty := by
        sorry

      have f_suplevelset_nonempty : (superlevel_set f_nor l).Nonempty :=
        have h1 : ∀ x, 0 ≤ f_nor x := by intro; exact f_nor_nonneg _
        have h2 : l < essSup f_nor volume := by rwa [f_nor_essSup_eq_one]
        nonempty_of_superlevel_set_of_bddBelow _ h1 h2
      have g_suplevelset_nonempty : (superlevel_set g_nor l).Nonempty :=
        have h1 : ∀ x, 0 ≤ g_nor x := by intro; exact g_nor_nonneg _
        have h2 : l < essSup g_nor volume := by rwa [g_nor_essSup_eq_one]
        nonempty_of_superlevel_set_of_bddBelow _ h1 h2

      have A_nonempty : A.Nonempty := ϕ_preimage_nonempty f_suplevelset_nonempty
      have B_nonempty : B.Nonempty := ϕ_preimage_nonempty g_suplevelset_nonempty

      have A_nm : NullMeasurableSet A := by
        unfold A
        -- rw [MeasurableEquiv.measurableSet_preimage _]
        -- refine measurable_superlevel_set_of_measurable ?_ _
        sorry
      have B_nm : NullMeasurableSet B := by
        unfold B
        sorry

      have ABC : A + B ⊆ C := by
        -- preimage_mono
        sorry -- use superlevel_sets_subset

      calc
        volume (superlevel_set f_nor l) + volume (superlevel_set g_nor l)
          = volume A + volume B := by iterate 2 rw [ϕ_preserves_volume]
        _ ≤ volume C :=
          one_dim_BMInequality_of_nullmeasurable A B C
            A_nonempty B_nonempty A_nm B_nm ABC
        _ = volume (superlevel_set h_nor l) := ϕ_preserves_volume

    -- use nonneg_integrable_integral_eq_integral_superlevel_set_meas
    sorry

  -- (∫ x, f x) + (∫ x, g x) ≤ (∫ x, h x) holds if f and g are not a.e. zero
  have integral_sum_le : (∫ x, f x) + (∫ x, g x) ≤ (∫ x, h x) := by
    sorry

  have weighted_AM_GM_var (a b : ℝ) (ha_nonneg : 0 ≤ a) (hb_nonneg : 0 ≤ b) :
      a ^ (1 - t) * b ^ t ≤ (1 - t) ^ (1 - t) * t ^ t * (a + b) := by
    suffices a ^ (1 - t) * b ^ t / ((1 - t) ^ (1 - t) * t ^ t)
        ≤ a + b by
      apply (div_le_iff₀' ?_).mp this
      exact mul_pos (by positivity) (by positivity)
    calc
      a ^ (1 - t) * b ^ t / ((1 - t) ^ (1 - t) * t ^ t)
        = (a / (1 - t)) ^ (1 - t) * (b / t) ^ t := by
          rw [mul_div_mul_comm,
            Real.div_rpow ha_nonneg (le_of_lt one_sub_t_pos),
            Real.div_rpow hb_nonneg t_nonneg]
      _ ≤ (1 - t) * (a / (1 - t)) + t * (b / t) := by
        refine Real.geom_mean_le_arith_mean2_weighted ?_ ?_ ?_ ?_ ?_
        · exact le_of_lt one_sub_t_pos
        · positivity
        · positivity
        · positivity
        · norm_num
      _ = a + b := by
        iterate 2 rw [mul_div_cancel₀]
        · exact h0t.ne'
        · exact one_sub_t_pos.ne'

  apply le_trans
    ( weighted_AM_GM_var (∫ x, f x) (∫ x, g x)
      (integral_nonneg hf_nonneg) (integral_nonneg hg_nonneg) )
  gcongr -- this solves the goal using integral_sum_le
