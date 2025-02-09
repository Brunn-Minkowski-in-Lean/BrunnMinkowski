import Mathlib.MeasureTheory.Function.L1Space
import Mathlib.MeasureTheory.Group.Measure

import BrunnMinkowski.EuclideanSpace

open Real Set Pointwise MeasureTheory MeasureTheory.Measure Filter

lemma meas_le_meas_add_right {α : Type u_1}
    [MeasurableSpace α] [AddGroup α] [MeasurableAdd α]
    {μ : Measure α} [μ.IsAddRightInvariant]
    (A B : Set α) (hB_nonempty : B.Nonempty)
    : μ A ≤ μ (A + B) := by
  obtain ⟨b, hb⟩ := hB_nonempty
  calc
    μ A = μ (A + {b}) := by
      rw [add_singleton, image_add_right, measure_preimage_add_right]
    _ ≤ μ (A + B) :=
        measure_mono (add_subset_add_left (singleton_subset_iff.mpr hb))

---- Superlevel sets ----
noncomputable def superlevel_set (f : ℝn n → ℝ) (c : ℝ) : Set (ℝn n)
  := {x | c < f x}

lemma measurable_ray {c : ℝ} : MeasurableSet {y | c < y} :=
  measurableSet_Ioi

lemma measurable_superlevel_set_of_measurable
    {f : ℝn n → ℝ} (hf_measurable : Measurable f)
    (c : ℝ) :
    MeasurableSet (superlevel_set f c) := by
  have measurable_ray_c : MeasurableSet {y | c < y} := measurable_ray
  rw [superlevel_set]
  -- 'measurability' can replace the below lines
  simp_all only [measurableSet_setOf]
  exact Measurable.comp' measurable_ray_c hf_measurable

lemma nullmeasurable_superlevel_set_of_aemeasurable
    {f : ℝn n → ℝ} (hf_aemeasurable : AEMeasurable f)
    (c : ℝ) :
    NullMeasurableSet (superlevel_set f c) := by
  have measurable_ray_c : MeasurableSet {y | c < y} := measurable_ray
  rw [superlevel_set]
  sorry

---- essSup ----
lemma nonneg_essSup_of_nonneg {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [hμ_ne0 : NeZero μ]
    {f : α → ℝ} (hf_nonneg : 0 ≤ f)
    : 0 ≤ essSup f μ := by
  rw [essSup_eq_sInf]
  apply Real.sInf_nonneg
  intros y hy
  rw [mem_setOf_eq] at hy
  by_contra hy_neg
  rw [not_le] at hy_neg
  have : 0 < μ {x | y < f x} :=
    calc
      0 < μ univ := measure_univ_pos.mpr hμ_ne0.ne
      _ = μ {x | y < f x} := by
        suffices {x | y < f x} = univ by rw [this]
        apply eq_univ_of_forall
        intro x
        exact lt_of_lt_of_le hy_neg (hf_nonneg x)
  rwa [hy, lt_self_iff_false] at this

lemma pos_essSup_of_integrable {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [hμ_ne0 : NeZero μ]
    {f : α → ℝ} (hf_nonneg : 0 ≤ f) (hf_supp_meas_ne0 : μ f.support ≠ 0)
    (hf_ess_bdd : IsBoundedUnder (fun (x1 x2 : ℝ) ↦ x1 ≤ x2) (ae μ) f)
    : 0 < essSup f μ := by
  have h1 : μ {y : α | essSup f μ < f y} = 0 := by

    sorry
  have h2 : f.support = {y : α | 0 < f y} := by
    unfold Function.support
    refine eq_of_subset_of_subset ?_ ?_
    all_goals
      rw [setOf_subset_setOf]
      intro x hx
    · exact Ne.lt_of_le hx.symm (hf_nonneg x)
    · exact ne_of_gt hx
  have hnonneg : 0 ≤ essSup f μ := nonneg_essSup_of_nonneg hf_nonneg
  have hne0 : essSup f μ ≠ 0 := by
    by_contra hzero
    suffices μ f.support = 0 by contradiction
    nth_rw 1 [h2, ← hzero]
    exact h1
  exact Ne.lt_of_le hne0.symm hnonneg

lemma pos_meas_supp_of_essSup_ne0 {α : Type*}
    {m : MeasurableSpace α} {μ : Measure α} [NeZero μ]
    {f : α → ℝ} (hf_essSup_ne0 : essSup f μ ≠ 0) :
    0 < μ f.support := by
  refine Ne.lt_of_le' ?_ (Measure.zero_le _ _)
  rw [ne_eq, ← univ_inter f.support, ← indicator_ae_eq_zero,
    indicator_univ]
  by_contra hf_ae_0
  have : essSup f μ = 0 := by
    calc
      essSup f μ
      _ = essSup 0 μ := essSup_congr_ae hf_ae_0
      _ = 0 := essSup_const' 0
  contradiction

lemma ae_zero_of_nonneg_essSup_zero_ess_bdd {α : Type u_1}
    [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf_nonneg : 0 ≤ f)
    (hf_ess_bdd : IsBoundedUnder (fun (x1 x2 : ℝ) ↦ x1 ≤ x2) (ae μ) f)
    (hf_essSup_zero : essSup f μ = 0) :
    f =ᵐ[μ] 0 := by
  have hf_ae_le_0 : f ≤ᵐ[μ] 0 := by
    unfold EventuallyLE
    simp only [Pi.zero_apply, ← hf_essSup_zero]
    exact ae_le_essSup hf_ess_bdd
  have hf_ae_ge_0 : 0 ≤ᵐ[μ] f := Eventually.of_forall hf_nonneg
  exact hf_ae_le_0.antisymm hf_ae_ge_0



-- #min_imports
