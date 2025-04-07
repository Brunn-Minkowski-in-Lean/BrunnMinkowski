--import Mathlib.MeasureTheory.Function.L1Space
--import Mathlib.MeasureTheory.Group.Measure
--import Mathlib.MeasureTheory.Integral.Bochner
--import Mathlib.MeasureTheory.Integral.Lebesgue
--import Mathlib.MeasureTheory.Integral.Layercake
--import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Integral.Layercake
-- import Mathlib.Data.Set.Basic
-- import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice

import BrunnMinkowski.EuclideanSpace

open Real Set Pointwise MeasureTheory MeasureTheory.Measure Filter

---- Basics ----
lemma le_of_forall_le_of_lt
    {a b : ℝ} (h : ∀ c, c < a → c ≤ b) :
    a ≤ b := by
    by_contra hba
    apply lt_of_not_le at hba
    obtain ⟨c, hac, hcb⟩ := exists_between hba
    exact not_lt_of_le (h c hcb) hac

lemma Ioo_disjoint_Ici_same
    {α : Type*} [LinearOrder α]
    {a b : α} :
    Disjoint (Ioo a b) (Ici b) := by
  rw [disjoint_left]
  exact fun _ hx hy ↦ hx.2.not_le hy

lemma meas_le_meas_add_right
    {α : Type u_1} [MeasurableSpace α] [AddGroup α] [MeasurableAdd α]
    {μ : Measure α} [μ.IsAddRightInvariant]
    (A B : Set α) (hB_nonempty : B.Nonempty)
    : μ A ≤ μ (A + B) := by
  obtain ⟨b, hb⟩ := hB_nonempty
  calc
    μ A
      = μ (A + {b}) := by
      rw [add_singleton, image_add_right, measure_preimage_add_right]
    _ ≤ μ (A + B) :=
        measure_mono (add_subset_add_left (singleton_subset_iff.mpr hb))

---- Superlevel sets ----
noncomputable def superlevel_set
    {α β : Type*} [LT β] (f : α → β) (c : β) :
    Set α := {x | c < f x}

lemma measurable_superlevel_set_of_measurable
    {f : ℝn n → ℝ} (hf_measurable : Measurable f)
    (c : ℝ) :
    MeasurableSet (superlevel_set f c) :=
  measurableSet_lt measurable_const hf_measurable

lemma nullmeasurable_superlevel_set_of_aemeasurable
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α := by volume_tac)
    {f : α → ℝ} (hf_aemeasurable : AEMeasurable f μ)
    (c : ℝ) :
    NullMeasurableSet (superlevel_set f c) μ :=
  nullMeasurableSet_lt aemeasurable_const hf_aemeasurable


lemma fin_vol_of_superlevelset_of_nonneg_integrable
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    {f : α → ℝ} (hf_nonneg : 0 ≤ f) (hf_integrable : Integrable f μ)
    {c : ℝ} (hc_pos : 0 < c) :
    μ (superlevel_set f c) < ⊤ := by

  let s := superlevel_set f c
  let f_ennreal : α → ENNReal := fun x ↦ (ENNReal.ofReal (f x))
  let g : α → ENNReal := indicator s (fun _ ↦ (ENNReal.ofReal c))

  have s_nullmeas : NullMeasurableSet s μ :=
    nullmeasurable_superlevel_set_of_aemeasurable μ
      (Integrable.aemeasurable hf_integrable) c

  have g_le_f_ennreal : g ≤ f_ennreal := by
    intro x; unfold g f_ennreal
    rcases @or_not (x ∈ s) with ha_mem_s | ha_not_mem_s
    · rw [indicator_of_mem ha_mem_s]
      rw [ENNReal.ofReal_le_ofReal_iff (hf_nonneg x)]
      exact le_of_lt (Membership.mem.out ha_mem_s)
    · rw [indicator_of_not_mem ha_not_mem_s]
      exact zero_le _

  refine ENNReal.lt_top_of_mul_ne_top_right ?_
    (pos_iff_ne_zero.mp (ENNReal.ofReal_pos.mpr hc_pos))
  apply ne_of_lt

  calc
    (ENNReal.ofReal c) * μ s
      = (∫⁻ x, g x ∂μ) := (lintegral_indicator_const₀ s_nullmeas _).symm
    _ ≤ (∫⁻ x, f_ennreal x ∂μ) := lintegral_mono g_le_f_ennreal
    _ < ⊤ := by
      refine (hasFiniteIntegral_iff_ofReal ?_).mp
        (Integrable.hasFiniteIntegral hf_integrable)
      apply ae_of_all
      simp only [Pi.zero_apply]
      exact hf_nonneg


lemma ofReal_integral_eq_lintegral_ofReal'
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α := by volume_tac)
    {f : α → ℝ} (hf_nonneg : 0 ≤ f) (hf_integrable : Integrable f μ) :
    ENNReal.ofReal (∫ x, f x ∂μ) = ∫⁻ x, ENNReal.ofReal (f x) ∂μ :=
  ofReal_integral_eq_lintegral_ofReal hf_integrable
    (ae_of_all _ (fun _ ↦ hf_nonneg _))

lemma lintegral_eq_lintegral_meas_superlevelset
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α := by volume_tac)
    {f : α → ℝ} (hf_nonneg : 0 ≤ f) (hf_integrable : Integrable f μ) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ
      = ∫⁻ t, indicator (Ioi 0) (fun y ↦ (μ (superlevel_set f y))) t ∂volume := by
  rw [lintegral_indicator measurableSet_Ioi]
  exact lintegral_eq_lintegral_meas_lt μ
    (ae_of_all _ (fun _ ↦ hf_nonneg _))
    (Integrable.aemeasurable hf_integrable)

-- lemma integral_eq_integral_meas_superlevelset
--     {α : Type*} [MeasurableSpace α]
--     (μ : Measure α := by volume_tac)
--     {f : α → ℝ} (hf_integrable : Integrable f μ) (hf_nonneg : 0 ≤ f) :
--     ∫ x, f x ∂μ =
--       ∫ t, indicator (Ioi 0) (fun y ↦ (μ (superlevel_set f y)).toReal) t := by
--   rw [integral_indicator measurableSet_Ioi]
--   refine Integrable.integral_eq_integral_meas_lt hf_integrable ?_
--   exact ae_of_all _ (fun _ ↦ hf_nonneg _)

-- lemma integrable_of_meas_superlevelset
--     {α : Type*} [MeasurableSpace α]
--     (μ : Measure α := by volume_tac)
--     {f : α → ℝ} (hf_nonneg : 0 ≤ f) (hf_integrable : Integrable f μ) :
--     Integrable (indicator (Ioi 0) (fun y ↦ (μ (superlevel_set f y)).toReal))
--     := by
--   constructor
--   ·
--     sorry
--   · rw [hasFiniteIntegral_iff_ofReal
--       (ae_of_all _ (indicator_nonneg (fun _ _ ↦ ENNReal.toReal_nonneg)))]
--     suffices ∫⁻ (a : ℝ), (Ioi 0).indicator
--         (fun x ↦ μ (superlevel_set f x)) a < ⊤ by
--       refine lt_of_eq_of_lt ?_ this
--       congr; funext a
--       rcases @or_not (a ∈ Ioi 0) with h0a | ha0
--       · simp only [indicator_of_mem h0a, ENNReal.ofReal_toReal_eq_iff, ne_eq]
--         exact ne_of_lt (fin_vol_of_superlevelset_of_nonneg_integrable
--           hf_nonneg hf_integrable h0a)
--       · simp only [indicator_of_not_mem ha0, ENNReal.ofReal_zero]

--     rw [lintegral_indicator measurableSet_Ioi]
--     unfold superlevel_set
--     rw [← lintegral_eq_lintegral_meas_lt μ
--       (ae_of_all _ (fun _ ↦ hf_nonneg _))
--       (Integrable.aemeasurable hf_integrable)]
--     exact Integrable.lintegral_lt_top hf_integrable

---- essSup ----
abbrev IsEssBdd
    {α β : Type*}
    [MeasurableSpace α] [ConditionallyCompleteLattice β]
    (f : α → β) (μ : Measure α := by volume_tac) :=
  IsBoundedUnder (fun (x1 x2 : β) ↦ x1 ≤ x2) (ae μ) f


lemma pos_meas_of_superlevel_set_of_bddBelow
    {α β : Type*}
    [MeasurableSpace α] [ConditionallyCompleteLinearOrder β]
    (μ : Measure α := by volume_tac) [NeZero μ]
    {f : α → β}
    {a : β} (ha : ∀ (x : α), a ≤ f x)
    {b : β} (hb : b < essSup f μ) :
    0 < μ (superlevel_set f b) := by
  rw [essSup_eq_sInf] at hb
  have : BddBelow {y | μ {x | y < f x} = 0} := by
    use a
    intro y
    rw [← not_imp_not, not_le, mem_setOf_eq]
    intro hy
    have : {x | y < f x} = univ := by
      apply eq_univ_of_forall
      intro
      exact lt_of_lt_of_le hy (ha _)
    rwa [this, measure_univ_eq_zero, ← ne_eq, ← neZero_iff]
  have : b ∉ {y | μ {x | y < f x} = 0} := not_mem_of_lt_csInf hb this
  rw [mem_setOf_eq] at this
  exact Ne.lt_of_le' this (Measure.zero_le μ _)


lemma nonempty_of_superlevel_set_of_bddBelow
    {α β : Type*}
    [MeasurableSpace α] [ConditionallyCompleteLinearOrder β]
    (μ : Measure α := by volume_tac) [NeZero μ]
    {f : α → β}
    {a : β} (ha : ∀ (x : α), a ≤ f x)
    {b : β} (hb : b < essSup f μ) :
    (superlevel_set f b).Nonempty :=
  nonempty_of_measure_ne_zero
    (ne_of_gt (pos_meas_of_superlevel_set_of_bddBelow _ ha hb))


lemma nonneg_essSup_of_nonneg
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [hμ_neZero : NeZero μ]
    {f : α → ℝ} (hf_nonneg : 0 ≤ f) :
    0 ≤ essSup f μ := by
  rw [essSup_eq_sInf]
  apply Real.sInf_nonneg
  intros y hy
  rw [mem_setOf_eq] at hy
  by_contra hy_neg
  rw [not_le] at hy_neg
  have : 0 < μ {x | y < f x} :=
    calc
      0 < μ univ := measure_univ_pos.mpr hμ_neZero.ne
      _ = μ {x | y < f x} := by
        suffices {x | y < f x} = univ by rw [this]
        apply eq_univ_of_forall
        intro x
        exact lt_of_lt_of_le hy_neg (hf_nonneg x)
  rwa [hy, lt_self_iff_false] at this


lemma ae_zero_of_nonneg_essSup_zero_essBdd
    {α : Type u_1} [MeasurableSpace α]
    {μ : Measure α}
    {f : α → ℝ} (hf_nonneg : 0 ≤ f)
    (hf_essBdd : IsEssBdd f μ) (hf_essSup_zero : essSup f μ = 0) :
    f =ᵐ[μ] 0 := by
  have hf_ae_le_0 : f ≤ᵐ[μ] 0 := by
    unfold EventuallyLE
    simp only [Pi.zero_apply, ← hf_essSup_zero]
    exact ae_le_essSup hf_essBdd
  have hf_ae_ge_0 : 0 ≤ᵐ[μ] f := Eventually.of_forall hf_nonneg
  exact hf_ae_le_0.antisymm hf_ae_ge_0


-- Under some conditions, essSup (f / b) = (essSup f) / b
lemma div_essSup_of_essBdd_lowerBdd
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α := by volume_tac) [NeZero μ]
    {f : α → ℝ} (hf_essBdd : IsEssBdd f μ)
    {a : ℝ} (ha_le_f : ∀ (x : α), a ≤ f x)
    {b : ℝ} (hb_pos : b > 0) :

    essSup (fun x ↦ (f x) / b) μ = (essSup f μ) / b := by

  iterate 2 rw [essSup_eq_sInf]
  refine le_antisymm ?_ ?_
  · apply le_of_forall_le_of_lt
    intro c hc
    rw [le_div_iff₀ hb_pos]
    refine le_csInf ?_ ?_
    · use essSup f μ
      rw [mem_setOf_eq, meas_essSup_lt]
    · intro d hd
      rw [mem_setOf_eq] at hd
      have : BddBelow {d | μ {x | d < f x / b} = 0} := by
        use a / b
        intro y
        rw [← not_imp_not, not_le, mem_setOf_eq]
        intro hy
        have : {x | y < f x / b} = univ := by
          apply eq_univ_of_forall
          intro x
          calc
            y < a / b := hy
            _ ≤ f x / b := by gcongr; exact ha_le_f x
        rwa [this, measure_univ_eq_zero, ← ne_eq, ← neZero_iff]
      have hc := not_mem_of_lt_csInf hc this
      rw [mem_setOf_eq] at hc
      by_contra hdcb
      rw [not_le] at hdcb
      suffices 0 < μ {x | d < f x} by exact (ne_of_lt this) hd.symm
      calc
        0 < μ {x | c < f x / b} :=
          Ne.lt_of_le' hc (Measure.zero_le μ {x | c < f x / b})
        _ ≤ μ {x | d < f x} := by
          apply measure_mono
          rw [setOf_subset_setOf]
          intro e he
          apply lt_trans hdcb
          rwa [← lt_div_iff₀ hb_pos]
  · apply le_of_forall_le_of_lt
    intro c hc
    rw [lt_div_iff₀ hb_pos] at hc
    refine le_csInf ?_ ?_
    · use (essSup f μ) / b
      simp only [mem_setOf_eq, div_lt_div_iff_of_pos_right hb_pos]
      exact meas_essSup_lt
    · intro d hd
      rw [mem_setOf_eq] at hd
      have : BddBelow {d | μ {x | d < f x} = 0} := by
        use a
        intro y
        rw [← not_imp_not, not_le, mem_setOf_eq]
        intro hy
        have : {x | y < f x} = univ := by
          apply eq_univ_of_forall
          intro x
          calc
            y < a := hy
            _ ≤ f x := ha_le_f x
        rwa [this, measure_univ_eq_zero, ← ne_eq, ← neZero_iff]
      have hc := not_mem_of_lt_csInf hc this
      rw [mem_setOf_eq] at hc
      by_contra hdc
      rw [not_le] at hdc
      suffices 0 < μ {x | d < f x / b} by exact (ne_of_lt this) hd.symm
      calc
        0 < μ {x | c * b < f x} :=
          Ne.lt_of_le' hc (Measure.zero_le μ {x | c * b < f x})
        _ ≤ μ {x | d < f x / b} := by
          apply measure_mono
          rw [setOf_subset_setOf]
          intro e he
          apply lt_trans hdc
          rwa [lt_div_iff₀ hb_pos]


-- !!!! NOT USED !!!!
-- If f is
-- · nonnegative,
-- · has support of nonzero measure,
-- · and is essentially bounded,
-- then the essential supremum of f is positive.
-- lemma pos_essSup_of_nonneg_posmeassupp_essBdd
--     {α : Type*} [MeasurableSpace α]
--     {μ : Measure α} [NeZero μ]
--     {f : α → ℝ} (hf_nonneg : 0 ≤ f) (hf_supp_meas_nonzero : μ f.support ≠ 0)
--     (hf_essBdd : IsEssBdd f μ) :
--     0 < essSup f μ := by
--   have h1 : μ {y : α | essSup f μ < f y} = 0 := meas_essSup_lt
--   have h2 : f.support = {y : α | 0 < f y} := by
--     unfold Function.support
--     refine eq_of_subset_of_subset ?_ ?_
--     all_goals
--       rw [setOf_subset_setOf]
--       intro x hx
--     · exact Ne.lt_of_le hx.symm (hf_nonneg x)
--     · exact ne_of_gt hx
--   have essSup_nonneg : 0 ≤ essSup f μ := nonneg_essSup_of_nonneg hf_nonneg
--   have essSup_nonzero : essSup f μ ≠ 0 := by
--     by_contra hzero
--     suffices μ f.support = 0 by contradiction
--     nth_rw 1 [h2, ← hzero]
--     exact h1
--   exact Ne.lt_of_le essSup_nonzero.symm essSup_nonneg


-- If f has nonzero essential supremum,
-- then it has support of nonzero measure.
-- lemma pos_meas_supp_of_essSup_nonzero
--     {α : Type*} [MeasurableSpace α]
--     {μ : Measure α} [NeZero μ]
--     {f : α → ℝ} (hf_essSup_nonzero : essSup f μ ≠ 0) :
--     0 < μ f.support := by
--   refine Ne.lt_of_le' ?_ (Measure.zero_le _ _)
--   rw [ne_eq, ← univ_inter f.support, ← indicator_ae_eq_zero,
--     indicator_univ]
--   by_contra hf_ae_0
--   have : essSup f μ = 0 := by
--     calc
--       essSup f μ
--       _ = essSup 0 μ := essSup_congr_ae hf_ae_0
--       _ = 0 := essSup_const' 0
--   contradiction

-- lemma hessSup_bdd_of_div_of_nonneg_essBdd {f : ℝn 1 → ℝ}
--     (hf_nonneg : 0 ≤ f) (hf_essBdd : IsEssBdd f volume)
--     {c : ℝ} (hc_nonneg : 0 ≤ c) :
--     0 ≤ essSup (fun x ↦ (f x) / c) volume ∧
--       essSup (fun x ↦ (f x) / c) volume ≤ (essSup f volume) / c := by
--   let f_div := fun x ↦ (f x) / c
--   have f_div_nonneg : 0 ≤ f_div := by
--     intro; exact div_nonneg (hf_nonneg _) hc_nonneg
--   constructor
--   · exact nonneg_essSup_of_nonneg f_div_nonneg
--   · have : f_div ≤ᵐ[volume] (fun _ ↦ (essSup f volume) / c) := by
--       refine Eventually.mono (ae_le_essSup hf_essBdd) ?_
--       intro x hx
--       exact div_le_div_of_nonneg_right hx hc_nonneg
--     calc
--       essSup f_div volume
--         ≤ essSup (fun (_ : ℝn 1) ↦ (essSup f volume) / c) volume :=
--           limsup_le_limsup this
--             (isCoboundedUnder_le_of_le (ae volume) f_div_nonneg)
--             (isBoundedUnder_const)
--       _ = (essSup f volume) / c := essSup_const' ((essSup f volume) / c)

-- #min_imports
