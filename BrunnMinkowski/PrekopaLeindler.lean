import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

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
      [AddCommGroup α] → [TopologicalSpace α] →  [IsTopologicalAddGroup α] → [T2Space α] → [Module ℝ α] → [ContinuousSMul ℝ α] → [FiniteDimensional ℝ α] → Sort}
    {base0 : P (EuclideanSpace ℝ (Fin 0))}
    {base1 : P ℝ}
    {induct : {α β : Type} →
      [AddCommGroup α] → [TopologicalSpace α] →  [IsTopologicalAddGroup α] → [T2Space α] → [Module ℝ α] → [ContinuousSMul ℝ α] → [FiniteDimensional ℝ α] →
      [AddCommGroup β] → [TopologicalSpace β] →  [IsTopologicalAddGroup β] → [T2Space β] → [Module ℝ β] → [ContinuousSMul ℝ β] → [FiniteDimensional ℝ β] →
      P α → P β → P (α × β)} :
  (α : Type) → [AddCommGroup α] → [TopologicalSpace α] →  [IsTopologicalAddGroup α] → [T2Space α] → [Module ℝ α] → [ContinuousSMul ℝ α] → [FiniteDimensional ℝ α] → P α := by sorry

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
        ⊆ A + B := add_subset_add hAm_subset_A hBm_subset_B
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
    · exact Nonempty.mono AmBmCm (Nonempty.add Am_nonempty Bm_nonempty)

  rw [hAm_vol_eq, hBm_vol_eq, measure_toMeasurable C] at hAmBmCm_vol
  exact hAmBmCm_vol

abbrev PL_dim1_cond (t : ℝ) (f g h : ℝn 1 → ℝ) :=
  (x y : ℝn 1) →
    (f x) ^ (1 - t) * (g y) ^ t ≤ h (x + y)

abbrev PL_dim1_conclusion (t : ℝ) (f g h : ℝn 1 → ℝ) :=
  (∫ x, f x) ^ (1 - t) * (∫ y, g y) ^ t
    ≤ (1 - t) ^ (1 - t) * t ^ t * (∫ x, h x)


/-
One-dim Prékopa--Leindler holds for all (f,g)
where f and g are essentially bounded.
-/
lemma prepkopa_leindler_dim1_essBdd
    {t : ℝ} (h0t : 0 < t) (ht1 : t < 1)
    {f g h : ℝn 1 → ℝ}
    (hf_nonneg : 0 ≤ f) (hf_integrable : Integrable f)
    (hg_nonneg : 0 ≤ g) (hg_integrable : Integrable g)
    (hh_nonneg : 0 ≤ h) (hh_integrable : Integrable h)
    (hf_essBdd : IsEssBdd f) (hg_essBdd : IsEssBdd g)
    (hfgh_pow_le : PL_dim1_cond t f g h) :
    PL_dim1_conclusion t f g h := by

  -- abbreviations
  let f_essBdd := IsEssBdd f
  let g_essBdd := IsEssBdd g

  -- conditions on t
  have one_sub_t_pos : 0 < 1 - t := sub_pos.mpr ht1
  have t_nonneg : 0 ≤ t := le_of_lt h0t

  -- essential supremums
  let f_essSup : ℝ := essSup f volume
  let g_essSup : ℝ := essSup g volume
  let h_essSup : ℝ := essSup h volume

  have f_essSup_nonneg : 0 ≤ f_essSup := nonneg_essSup_of_nonneg hf_nonneg
  have g_essSup_nonneg : 0 ≤ g_essSup := nonneg_essSup_of_nonneg hg_nonneg

  have superlevel_sets_subset {f g h : ℝn 1 → ℝ}
      {l : ℝ} (hl_pos : 0 < l)
      (hfgh_pow_le : PL_dim1_cond t f g h) :
      superlevel_set f l + superlevel_set g l ⊆ superlevel_set h l := by
    refine add_subset_iff.mpr ?_
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
    rw [PL_dim1_conclusion, this, Real.zero_rpow (by positivity), zero_mul]
    exact mul_nonneg (by positivity) (integral_nonneg hh_nonneg)
  by_cases hg_ae_zero : g =ᵐ[volume] 0
  · -- Assume g is a.e. zero
    have : (∫ x, g x) = 0 := integral_eq_zero_of_ae hg_ae_zero
    rw [PL_dim1_conclusion, this, Real.zero_rpow (by positivity), mul_zero]
    exact mul_nonneg (by positivity) (integral_nonneg hh_nonneg)

  have f_essSup_pos : 0 < f_essSup := by
    by_contra hf_essSup_zero
    have hf_essSup_zero := le_antisymm (not_lt.mp hf_essSup_zero) f_essSup_nonneg
    have := ae_zero_of_nonneg_essSup_zero_essBdd
      hf_nonneg hf_essBdd hf_essSup_zero
    contradiction
  have g_essSup_pos : 0 < g_essSup := by
    by_contra hg_essSup_zero
    have hg_essSup_zero := le_antisymm (not_lt.mp hg_essSup_zero) g_essSup_nonneg
    have := ae_zero_of_nonneg_essSup_zero_essBdd
      hg_nonneg hg_essBdd hg_essSup_zero
    contradiction

  -- normalize by essential supremums
  let f_nor : ℝn 1 → ℝ := fun x ↦ (f x) / f_essSup
  let g_nor : ℝn 1 → ℝ := fun x ↦ (g x) / g_essSup
  let h_nor : ℝn 1 → ℝ := fun x ↦ (h x) / (f_essSup ^ (1 - t) * g_essSup ^ t)

  have f_nor_nonneg : 0 ≤ f_nor := by
    intro; exact div_nonneg (hf_nonneg _) f_essSup_nonneg
  have g_nor_nonneg : 0 ≤ g_nor := by
    intro; exact div_nonneg (hg_nonneg _) g_essSup_nonneg
  have h_nor_nonneg : 0 ≤ h_nor := by
    intro; exact div_nonneg (hh_nonneg _) (by positivity)

  have f_nor_integrable : Integrable f_nor := Integrable.div_const hf_integrable _
  have g_nor_integrable : Integrable g_nor := Integrable.div_const hg_integrable _
  have h_nor_integrable : Integrable h_nor := Integrable.div_const hh_integrable _

  have f_nor_essBdd : IsEssBdd f_nor := by
    have (a b : ℝ) : a ≤ b → (a / f_essSup) ≤ (b / f_essSup) :=
      (div_le_div_iff_of_pos_right f_essSup_pos).mpr
    exact IsBoundedUnder.comp this hf_essBdd
  have g_nor_essBdd : IsEssBdd g_nor := by
    have (a b : ℝ) : a ≤ b → (a / g_essSup) ≤ (b / g_essSup) :=
      (div_le_div_iff_of_pos_right g_essSup_pos).mpr
    exact IsBoundedUnder.comp this hg_essBdd

  have nor_integral_sum_le :
      (∫ x, f_nor x) + (∫ x, g_nor x) ≤ (∫ x, h_nor x) := by

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
      simp only
      gcongr
      exact hfgh_pow_le x y

    have fgh_nor_splsets_vol_ineq
        {l : ℝ} (h0l : 0 < l) (hl1 : l < 1) :
        volume (superlevel_set f_nor l) + volume (superlevel_set g_nor l)
          ≤ volume (superlevel_set h_nor l) := by

      let φ₁ : ℝn 1 ≃ᵐ (Fin 1 → ℝ) := (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm
      let φ₂ : (Fin 1 → ℝ) ≃ᵐ ℝ := MeasurableEquiv.funUnique (Fin 1) ℝ
      let φ : ℝn 1 ≃ᵐ ℝ := φ₁.trans φ₂

      let A : Set ℝ := φ '' (superlevel_set f_nor l)
      let B : Set ℝ := φ '' (superlevel_set g_nor l)
      let C : Set ℝ := φ '' (superlevel_set h_nor l)

      have φ_measpres : MeasurePreserving φ volume volume :=
        MeasurePreserving.trans
          (PiLp.volume_preserving_ofLp (Fin 1))
          (volume_preserving_funUnique (Fin 1) ℝ)

      have φ_preserves_volume {D : Set (ℝn 1)} :
          volume (φ '' D) = volume D := by
        rw [← φ_measpres.measure_preimage_equiv (φ '' D),
          MeasurableEquiv.preimage_image]

      have f_suplevelset_nonempty : (superlevel_set f_nor l).Nonempty :=
        have h1 (x : ℝn 1) : 0 ≤ f_nor x := f_nor_nonneg x
        have h2 : l < essSup f_nor volume := by rwa [f_nor_essSup_eq_one]
        nonempty_of_superlevel_set_of_bddBelow _ h1 h2
      have g_suplevelset_nonempty : (superlevel_set g_nor l).Nonempty :=
        have h1 (x : ℝn 1) : 0 ≤ g_nor x := g_nor_nonneg x
        have h2 : l < essSup g_nor volume := by rwa [g_nor_essSup_eq_one]
        nonempty_of_superlevel_set_of_bddBelow _ h1 h2

      have A_nonempty : A.Nonempty := Nonempty.image φ f_suplevelset_nonempty
      have B_nonempty : B.Nonempty := Nonempty.image φ g_suplevelset_nonempty

      have A_B_nm : NullMeasurableSet A ∧ NullMeasurableSet B := by
        unfold A B
        constructor; all_goals
          rw [MeasurableEquiv.image_eq_preimage_symm]
          refine NullMeasurableSet.preimage
            (nullmeasurable_superlevel_set_of_aemeasurable _
              (Integrable.aemeasurable ?_) l)
            (MeasurePreserving.quasiMeasurePreserving
              (MeasurePreserving.symm φ φ_measpres))
        · exact f_nor_integrable
        · exact g_nor_integrable

      have ABC : A + B ⊆ C := calc
        A + B
          ⊆ φ '' (superlevel_set f_nor l + superlevel_set g_nor l) := by
            unfold A B
            intro x hx
            obtain ⟨y, hy, z, hz, hyzx⟩ := mem_add.mp hx
            obtain ⟨yy, hyy, rfl⟩ := (Set.mem_image _ _ _).mp hy
            obtain ⟨zz, hzz, rfl⟩ := (Set.mem_image _ _ _).mp hz
            rw [← hyzx]
            have : φ yy + φ zz = φ (yy + zz) := by
              unfold φ φ₁ φ₂
              simp [MeasurableEquiv.trans_apply,
                MeasurableEquiv.funUnique_apply,
                MeasurableEquiv.toLp]
            rw [this]
            exact Set.mem_image_of_mem φ (add_mem_add hyy hzz)
        _ ⊆ C := Set.image_mono (nor_superlevel_sets_subset h0l)

      calc
        volume (superlevel_set f_nor l) + volume (superlevel_set g_nor l)
          = volume A + volume B := by iterate 2 rw [φ_preserves_volume]
        _ ≤ volume C :=
          one_dim_BMInequality_of_nullmeasurable A B C
            A_nonempty B_nonempty A_B_nm.1 A_B_nm.2 ABC
        _ = volume (superlevel_set h_nor l) := φ_preserves_volume


    rw [← ofReal_le_ofReal_iff (integral_nonneg h_nor_nonneg)]
    refine le_trans ENNReal.ofReal_add_le ?_
    rw [ofReal_integral_eq_lintegral_ofReal' _ f_nor_nonneg f_nor_integrable,
      ofReal_integral_eq_lintegral_ofReal' _ g_nor_nonneg g_nor_integrable,
      ofReal_integral_eq_lintegral_ofReal' _ h_nor_nonneg h_nor_integrable,
      lintegral_eq_lintegral_meas_superlevelset _ f_nor_nonneg f_nor_integrable,
      lintegral_eq_lintegral_meas_superlevelset _ g_nor_nonneg g_nor_integrable,
      lintegral_eq_lintegral_meas_superlevelset _ h_nor_nonneg h_nor_integrable]

    -- change Ioi 0 to Ioo 0 1
    let fun_vol_splset_f : ℝ → ℝ≥0∞ := fun l ↦ volume (superlevel_set f_nor l)
    let fun_vol_splset_g : ℝ → ℝ≥0∞ := fun l ↦ volume (superlevel_set g_nor l)
    let fun_vol_splset_h : ℝ → ℝ≥0∞ := fun l ↦ volume (superlevel_set h_nor l)

    have fg_integral_interval :
        ∫⁻ x, indicator (Ioo 0 1) fun_vol_splset_f x
          = ∫⁻ x, indicator (Ioi 0) fun_vol_splset_f x ∧
        ∫⁻ x, indicator (Ioo 0 1) fun_vol_splset_g x
          = ∫⁻ x, indicator (Ioi 0) fun_vol_splset_g x := by

      have f_nor_ae_le_one : ∀ᵐ (a : ℝn 1), f_nor a ≤ 1 := by
        rw [← f_nor_essSup_eq_one]
        exact ae_le_essSup
      have g_nor_ae_le_one : ∀ᵐ (a : ℝn 1), g_nor a ≤ 1 := by
        rw [← g_nor_essSup_eq_one]
        exact ae_le_essSup

      unfold fun_vol_splset_f fun_vol_splset_g superlevel_set
      constructor; all_goals
        congr; funext x
        simp only [← Ioo_union_Ici_eq_Ioi zero_lt_one,
          indicator_union_of_disjoint Ioo_disjoint_Ici_same]
        symm; refine Eq.trans ?_ (add_zero _)
        rw [ENNReal.add_right_inj]
        · simp only [indicator_apply_eq_zero]
          intro h1x
          rw [Set.mem_Ici] at h1x
          simp only [measure_eq_zero_iff_ae_notMem, mem_setOf_eq, not_lt]
          first
          | exact Eventually.mono f_nor_ae_le_one (fun _ hfx ↦ hfx.trans h1x)
          | exact Eventually.mono g_nor_ae_le_one (fun _ hfx ↦ hfx.trans h1x)
        · rcases @or_not (x ∈ Set.Ioo 0 1) with hx | hx
          · rw [indicator_of_mem hx]
            refine ne_of_lt (fin_vol_of_superlevelset_of_nonneg_integrable ?_ ?_ hx.1)
            · first | exact f_nor_nonneg | exact g_nor_nonneg
            · first | exact f_nor_integrable | exact g_nor_integrable
          · exact Eq.trans_ne (indicator_of_notMem hx _) zero_ne_top

    have h_integral_interval :
        ∫⁻ x, indicator (Ioo 0 1) fun_vol_splset_h x
          ≤ ∫⁻ x, indicator (Ioi 0) fun_vol_splset_h x := by
      apply lintegral_mono
      exact indicator_le_indicator_of_subset Ioo_subset_Ioi_self (zero_le _)

    rw [← fg_integral_interval.1, ← fg_integral_interval.2]
    refine le_trans ?_ h_integral_interval

    refine le_trans (le_lintegral_add _ _) (lintegral_mono ?_)
    rw [← Set.indicator_add]
    refine fun _ ↦ indicator_le_indicator' ?_
    exact fun h0x1 ↦ fgh_nor_splsets_vol_ineq h0x1.1 h0x1.2


  have weighted_AM_GM_var
      (a b : ℝ) (ha_nonneg : 0 ≤ a) (hb_nonneg : 0 ≤ b) :
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
      _ ≤ (1 - t) * (a / (1 - t)) + t * (b / t) :=
        Real.geom_mean_le_arith_mean2_weighted
          (le_of_lt one_sub_t_pos)
          (by positivity) (by positivity) (by positivity) (by norm_num)
      _ = a + b := by
        rw [mul_div_cancel₀ _ h0t.ne', mul_div_cancel₀ _ one_sub_t_pos.ne']

  have : (∫ x, f_nor x) ^ (1 - t) * (∫ x, g_nor x) ^ t
    ≤ (1 - t) ^ (1 - t) * t ^ t * (∫ x, h_nor x) := by
    have := weighted_AM_GM_var (∫ x, f_nor x) (∫ x, g_nor x)
      (integral_nonneg f_nor_nonneg) (integral_nonneg g_nor_nonneg)
    apply le_trans this
    gcongr


  unfold f_nor g_nor h_nor at this
  simp only [integral_div] at this
  rw [Real.div_rpow (integral_nonneg hf_nonneg) (by positivity),
    Real.div_rpow (integral_nonneg hg_nonneg) (by positivity)] at this
  field_simp at this
  exact this



/-
Fix f.
If One-dim Prékopa--Leindler holds for all (f,g) where g is essentially bounded,
then Prékopa--Leindler holds for all (f,g).
-/
lemma prepkopa_leindler_dim1_from_g_essBdd
    {t : ℝ} (h0t : 0 < t) -- (ht1 : t < 1)
    {f g h : ℝn 1 → ℝ}
    (hf_nonneg : 0 ≤ f) -- (hf_integrable : Integrable f)
    (hg_nonneg : 0 ≤ g) (hg_integrable : Integrable g)
    -- (hh_nonneg : 0 ≤ h) (hh_integrable : Integrable h)
    (hfgh_pow_le : PL_dim1_cond t f g h)
    (hgg_essBdd_true : {gg : ℝn 1 → ℝ} →
      (hgg_nonneg : 0 ≤ gg) → (hgg_integrable : Integrable gg) →
      (hgg_essBdd : IsEssBdd gg) →
      (hfggh_pow_le : PL_dim1_cond t f gg h) →
      PL_dim1_conclusion t f gg h) :
    PL_dim1_conclusion t f g h := by

  let g_cut (c : ℝ) := min g (fun _ ↦ c)

  have g_cut_nonneg {c : ℝ} (hc_nonneg : 0 ≤ c) : 0 ≤ g_cut c := by
    intro; exact le_min (hg_nonneg _) hc_nonneg

  have g_cut_le_g {c : ℝ} (hc_nonneg : 0 ≤ c) : g_cut c ≤ g := by
    intro; exact min_le_left _ _

  have g_cut_integrable {c : ℝ} (hc_nonneg : 0 ≤ c) :
      Integrable (g_cut c) := by
    refine Integrable.mono hg_integrable ?_ ?_
    · exact AEStronglyMeasurable.inf hg_integrable.1
        aestronglyMeasurable_const
    · apply ae_of_all
      simp only [norm_eq_abs,
        abs_of_nonneg (hg_nonneg _), abs_of_nonneg (g_cut_nonneg hc_nonneg _)]
      exact g_cut_le_g hc_nonneg

  have PL_dim1_conclusion_g_cut {c : ℝ} (hc_nonneg : 0 ≤ c) :
      PL_dim1_conclusion t f (g_cut c) h := by

    refine hgg_essBdd_true (g_cut_nonneg hc_nonneg) ?_ ?_ ?_
    · -- Integrable (g_cut c)
      exact g_cut_integrable hc_nonneg
    · -- IsEssBdd (g_cut c)
      have const_essBdd : IsEssBdd (fun (_ : ℝn 1) ↦ c) := by
        exact isBoundedUnder_const
      unfold IsEssBdd at *
      have g_cut_bdd_c : g_cut c ≤ᵐ[volume] fun (_ : ℝn 1) ↦ c := by
        apply ae_of_all
        simp only [g_cut, Pi.inf_apply, inf_le_right, implies_true]
      exact IsBoundedUnder.mono_le const_essBdd g_cut_bdd_c
    . -- PL_dim1_cond t f (g_cut c) h
      intro x y
      refine le_trans ?_ (hfgh_pow_le x y)
      gcongr
      · exact Real.rpow_nonneg (hf_nonneg x) (1 - t)
      · exact g_cut_nonneg hc_nonneg y
      · exact g_cut_le_g hc_nonneg y

  have : Tendsto (fun (n : ℕ) ↦ ∫ (x : ℝn 1), g_cut n x)
      atTop (𝓝 (∫ (x : ℝn 1), g x)) := by
    refine integral_tendsto_of_tendsto_of_monotone ?_ ?_ ?_ ?_
    · intro; exact g_cut_integrable (Nat.cast_nonneg _)
    · exact hg_integrable
    · -- g_cut is pointwise monotone
      apply ae_of_all
      intro a b c hbc
      simp only [g_cut, Pi.inf_apply]
      exact min_le_min (le_refl _) (Nat.cast_le.mpr hbc)
    · -- g_cut tends to g pointwise
      apply ae_of_all
      intro a
      apply tendsto_atTop_of_eventually_const
      case i₀ => exact Nat.ceil (g a)
      intro n hn
      apply min_eq_left
      exact le_trans (Nat.le_ceil (g a)) (Nat.cast_le.mpr hn)

  have : Tendsto (fun (n : ℕ) ↦ (∫ x, f x) ^ (1 - t) * (∫ y, g_cut n y) ^ t)
      atTop (𝓝 ((∫ x, f x) ^ (1 - t) * (∫ y, g y) ^ t)) := by
    conv in (occs := *) ((∫ (x : ℝn 1), f x) ^ (1 - t) * _) =>
      · rw [mul_comm]
      · rw [mul_comm]
    refine Tendsto.mul_const ((∫ (x : ℝn 1), f x) ^ (1 - t)) ?_
    exact Tendsto.rpow_const this (Or.inr (le_of_lt h0t))

  refine le_of_tendsto' this ?_
  intro c
  exact PL_dim1_conclusion_g_cut (by norm_num)


/-
Fix g.
If One-dim Prékopa--Leindler holds for all (f,g) where f is essentially bounded,
then Prékopa--Leindler holds for all (f,g).
-/
lemma prepkopa_leindler_dim1_from_f_essBdd
    {t : ℝ} (ht1 : t < 1)
    {f g h : ℝn 1 → ℝ}
    (hf_nonneg : 0 ≤ f) (hf_integrable : Integrable f)
    (hg_nonneg : 0 ≤ g)
    (hfgh_pow_le : PL_dim1_cond t f g h)
    (hff_essBdd_true : {ff : ℝn 1 → ℝ} →
      (hff_nonneg : 0 ≤ ff) → (hff_integrable : Integrable ff) →
      (hff_essBdd : IsEssBdd ff) →
      (hffgh_pow_le : PL_dim1_cond t ff g h) →
      PL_dim1_conclusion t ff g h) :
    PL_dim1_conclusion t f g h := by

  have PL_dim1_cond_swap {f g h : ℝn 1 → ℝ} :
      PL_dim1_cond t f g h ↔ PL_dim1_cond (1 - t) g f h := by
    have (t : ℝ) {f g h : ℝn 1 → ℝ} :
        PL_dim1_cond t f g h → PL_dim1_cond (1 - t) g f h := by
      intro hh x y
      rw [sub_sub_cancel 1 t, mul_comm, add_comm x y]
      exact hh y x
    constructor
    · exact this t
    · nth_rw 2 [← sub_sub_self 1 t]
      exact this (1 - t)

  have PL_dim1_conclusion_swap {f g h : ℝn 1 → ℝ} :
      PL_dim1_conclusion t f g h ↔ PL_dim1_conclusion (1 - t) g f h := by
    have (t : ℝ) {f g h : ℝn 1 → ℝ} :
        PL_dim1_conclusion t f g h → PL_dim1_conclusion (1 - t) g f h := by
      unfold PL_dim1_conclusion
      rw [sub_sub_cancel 1 t, mul_comm, mul_comm (t ^ t)]
      intro; assumption
    constructor
    · exact this t
    · nth_rw 2 [← sub_sub_self 1 t]
      exact this (1 - t)

  rw [PL_dim1_conclusion_swap]

  refine prepkopa_leindler_dim1_from_g_essBdd
    (sub_pos_of_lt ht1)
    hg_nonneg
    hf_nonneg hf_integrable
    ?_ ?_
  · rw [← PL_dim1_cond_swap]; exact hfgh_pow_le
  · intro ff hff_nonneg hff_integrable hff_essBdd hffgh_pow_le
    rw [← PL_dim1_cond_swap] at hffgh_pow_le
    rw [← PL_dim1_conclusion_swap]
    exact hff_essBdd_true hff_nonneg hff_integrable hff_essBdd hffgh_pow_le


-- One-dim Prékopa--Leindler holds for all (f,g) where f is essentially bounded.
lemma prekopa_leindler_dim1_f_essBdd
    {t : ℝ} (h0t : 0 < t) (ht1 : t < 1)
    {f g h : ℝn 1 → ℝ}
    (hf_nonneg : 0 ≤ f) (hf_integrable : Integrable f)
    (hg_nonneg : 0 ≤ g) (hg_integrable : Integrable g)
    (hh_nonneg : 0 ≤ h) (hh_integrable : Integrable h)
    (hf_essBdd : IsEssBdd f)
    (hfgh_pow_le : PL_dim1_cond t f g h) :
    PL_dim1_conclusion t f g h := by

  refine prepkopa_leindler_dim1_from_g_essBdd h0t
    hf_nonneg
    hg_nonneg hg_integrable
    hfgh_pow_le ?_

  intro gg hgg_nonneg hgg_integrable hgg_essBdd hfggh_pow_le
  exact prepkopa_leindler_dim1_essBdd h0t ht1
    hf_nonneg hf_integrable
    hgg_nonneg hgg_integrable
    hh_nonneg hh_integrable
    hf_essBdd hgg_essBdd
    hfggh_pow_le


-- One-dim Prékopa--Leindler
lemma prekopa_leindler_dim1
    {t : ℝ} (h0t : 0 < t) (ht1 : t < 1)
    {f g h : ℝn 1 → ℝ}
    (hf_nonneg : 0 ≤ f) (hf_integrable : Integrable f)
    (hg_nonneg : 0 ≤ g) (hg_integrable : Integrable g)
    (hh_nonneg : 0 ≤ h) (hh_integrable : Integrable h)
    (hfgh_pow_le : PL_dim1_cond t f g h) :
    PL_dim1_conclusion t f g h := by

  refine prepkopa_leindler_dim1_from_f_essBdd ht1
    hf_nonneg hf_integrable
    hg_nonneg
    hfgh_pow_le ?_

  intro ff hff_nonneg hff_integrable hff_essBdd hffgh_pow_le
  exact prekopa_leindler_dim1_f_essBdd h0t ht1
    hff_nonneg hff_integrable
    hg_nonneg hg_integrable
    hh_nonneg hh_integrable
    hff_essBdd
    hffgh_pow_le
