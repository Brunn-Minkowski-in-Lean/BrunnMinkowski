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

theorem prekopa_leindler
    {t : ℝ} (h0t : 0 < t) (ht1 : t < 1)
    {d : ℕ} (f g h : ℝn d → ℝ)
    (hf_nonneg : 0 ≤ f) (hf_integrable : Integrable f)
    (hf_nonneg : 0 ≤ g) (hg_integrable : Integrable g)
    (hf_nonneg : 0 ≤ h) (hh_integrable : Integrable h)
    (hlb :
      ∀ x y : ℝn d,
      (f x)^(1 - t) * (g y)^t ≤ h (x + y)) :
  (∫ x, f x)^(1-t) * (∫ y, g y)^t ≤
  (1 - t)^(d * (1-t)) * t^(d*t) * (∫ x, h x)
  := by sorry

lemma nonneg_integrable_integral_eq_integral_superlevel_set_meas
    {f : ℝn n → ℝ} (hf_nonneg : 0 ≤ f) (hf_integrable : Integrable f) :
    (∫ x, f x) = (∫ y, (fun l ↦ (volume (superlevel_set f l)).toReal) y) := by
  sorry


lemma prekopa_leindler_dim1
    {t : ℝ} (h0t : 0 < t) (ht1 : t < 1)
    {f g h : ℝn 1 → ℝ}
    (hf_nonneg : 0 ≤ f) (hf_integrable : Integrable f)
    (hg_nonneg : 0 ≤ g) (hg_integrable : Integrable g)
    (hh_nonneg : 0 ≤ h) (hh_integrable : Integrable h)
    (hlb :
      ∀ x y : ℝn 1,
      (f x) ^ (1 - t) * (g y) ^ t ≤ h (x + y)) :
    (∫ x, f x) ^ (1 - t) * (∫ y, g y) ^ t
      ≤ (1 - t) ^ (1 - t) * t ^ t * (∫ x, h x) := by

  let prekopa_leindler_dim1_conclusion :=
    (∫ x, f x) ^ (1 - t) * (∫ y, g y) ^ t
      ≤ (1 - t) ^ (1 - t) * t ^ t * (∫ x, h x)

  let f_ess_bdd := IsBoundedUnder (fun (x1 x2 : ℝ) ↦ x1 ≤ x2) (ae volume) f
  let g_ess_bdd := IsBoundedUnder (fun (x1 x2 : ℝ) ↦ x1 ≤ x2) (ae volume) g

  -- conditions on t
  have one_sub_t_pos : 0 < 1 - t := sub_pos.mpr ht1
  have t_nonneg : 0 ≤ t := le_of_lt h0t

  -- essential supremums
  let f_essSup : ℝ := essSup f volume
  let g_essSup : ℝ := essSup g volume
  let h_essSup : ℝ := essSup h volume

  have f_essSup_nonneg : f_essSup ≥ 0 := nonneg_essSup_of_nonneg hf_nonneg
  have g_essSup_nonneg : g_essSup ≥ 0 := nonneg_essSup_of_nonneg hg_nonneg
  have h_essSup_nonneg : h_essSup ≥ 0 := nonneg_essSup_of_nonneg hh_nonneg

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

  -- The conclusion holds when f or g 'has zero essential supremum and is essentially bounded'
  have prekopa_leindler_dim1_of_ess_bdd_essSup_zero
      (hf_or_g_cond : (f_ess_bdd ∧ f_essSup = 0) ∨ (g_ess_bdd ∧ g_essSup = 0)) :
      prekopa_leindler_dim1_conclusion := by

    unfold prekopa_leindler_dim1_conclusion
    rcases hf_or_g_cond with hf_cond | hg_cond
    · -- Assume f_ess_bdd and f_essSup = 0
      have hf_integral_eq_zero : (∫ x, f x) = 0 :=
        integral_eq_zero_of_ae
          (ae_zero_of_nonneg_essSup_zero_ess_bdd
            hf_nonneg hf_cond.1 hf_cond.2)
      rw [hf_integral_eq_zero, Real.zero_rpow (by positivity), zero_mul]
      exact mul_nonneg (by positivity) (integral_nonneg hh_nonneg)
    · -- Assume g_ess_bdd and g_essSup = 0
      have hg_integral_eq_zero : (∫ x, g x) = 0 :=
        integral_eq_zero_of_ae
          (ae_zero_of_nonneg_essSup_zero_ess_bdd
            hg_nonneg hg_cond.1 hg_cond.2)
      rw [hg_integral_eq_zero, Real.zero_rpow (by positivity), mul_zero]
      exact mul_nonneg (by positivity) (integral_nonneg hh_nonneg)

  -- (∫ x, f x) + (∫ x, g x) ≤ (∫ x, h x) holds if f and g are essentially bounded
  have integral_sum_le_of_ess_bdd_essSup_nonzero
      (hf_ess_bdd : f_ess_bdd) (hg_ess_bdd : g_ess_bdd)
      (hf_essSup_nonzero : f_essSup ≠ 0) (hg_essSup_nonzero : g_essSup ≠ 0)
      : (∫ x, f x) + (∫ x, g x) ≤ (∫ x, h x) := by

    -- normalize the essential supremums
    let f_nor : ℝn 1 → ℝ := fun x ↦ (f x) / f_essSup
    let g_nor : ℝn 1 → ℝ := fun x ↦ (g x) / g_essSup
    let h_nor : ℝn 1 → ℝ := fun x ↦ (h x) / (f_essSup ^ (1 - t) * g_essSup ^ t)

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
      exact hlb x y

    have {l : ℝ} (h0l : 0 < l) (hl1 : h < 1) :
        volume (superlevel_set f_nor l) + volume (superlevel_set g_nor l)
          ≤ volume (superlevel_set h_nor l) := by

      let ϕ : ℝ ≃ᵐ ℝn 1 := (MeasurableEquiv.funUnique (Fin 1) ℝ).symm
      let A : Set ℝ := ϕ ⁻¹' (superlevel_set f_nor l)
      let B : Set ℝ := ϕ ⁻¹' (superlevel_set g_nor l)
      let C : Set ℝ := ϕ ⁻¹' (superlevel_set h_nor l)
      -- use NullMeasurableSet.exists_measurable_subset_ae_eq and nullmeasurable_superlevel_set_of_aemeasurable to make measurable sets

      have ϕ_preserves_volume {D : Set (ℝn 1)} :
          volume (ϕ ⁻¹' D) = volume D := by
        -- MeasureTheory.volume_preserving_funUnique?
        -- MeasurableEquiv.funUnique?
        sorry

      have ϕ_preimage_nonempty {D : Set (ℝn 1)} (hD : D.Nonempty) :
          (ϕ ⁻¹' (D)).Nonempty := by
        sorry

      have f_suplevset_nonempty : (superlevel_set f_nor l).Nonempty := by
        sorry
      have g_suplevset_nonempty : (superlevel_set g_nor l).Nonempty := by
        sorry
      have h_suplevset_nonempty : (superlevel_set h_nor l).Nonempty := by
        sorry

      have nA : A.Nonempty := ϕ_preimage_nonempty f_suplevset_nonempty
      have nB : B.Nonempty := ϕ_preimage_nonempty g_suplevset_nonempty
      have nC : C.Nonempty := ϕ_preimage_nonempty h_suplevset_nonempty

      have mA : MeasurableSet A := by
        unfold A
        rw [MeasurableEquiv.measurableSet_preimage _]
        refine measurable_superlevel_set_of_measurable ?_ _
        sorry

      calc
        volume (superlevel_set f_nor l) + volume (superlevel_set g_nor l)
          = volume A + volume B := by iterate 2 rw [ϕ_preserves_volume]
        _ ≤ volume C := sorry
          -- one_dim_BMInequality A B C nA nB nC _ _ _ _
        _ = volume (superlevel_set h_nor l) := ϕ_preserves_volume

    sorry

  -- (∫ x, f x) + (∫ x, g x) ≤ (∫ x, h x) holds for arbitrary f and g
  have integral_sum_le : (∫ x, f x) + (∫ x, g x) ≤ (∫ x, h x) := by
    sorry

  /-

  rcases eq_or_ne f_essSup 0 with hf_essSup_zero | hf_essSup_ne0
  · -- Assume f_essSup = 0
    have hf_integral_eq_zero : (∫ x, f x) = 0 :=
      sorry
      -- integral_eq_zero_of_ae
      --   (ae_zero_of_essSup_zero_nonneg hf_nonneg hf_integrable hf_essSup_zero)
    rw [hf_integral_eq_zero, Real.zero_rpow (by positivity), zero_mul]
    exact mul_nonneg (by positivity) (integral_nonneg hh_nonneg)
  rcases eq_or_ne g_essSup 0 with hg_essSup_zero | hg_essSup_ne0
  · -- Assume g_essSup = 0
    have hg_integral_eq_zero : (∫ x, g x) = 0 :=
      sorry
      -- integral_eq_zero_of_ae
      --   (ae_zero_of_essSup_zero_nonneg hg_nonneg hg_integrable hg_essSup_zero)
    rw [hg_integral_eq_zero, Real.zero_rpow (by positivity), mul_zero]
    exact mul_nonneg (by positivity) (integral_nonneg hh_nonneg)

  have hh_essSup_pos : 0 < h_essSup := by
    have hfgh_supp_rel : f.support + g.support ⊆ h.support := by
      intros z hz
      rw [Set.mem_add] at hz
      choose x hx y hy hxyz using hz
      rw [Function.mem_support] at *
      have : 0 < f x := Ne.lt_of_le' hx (hf_nonneg x)
      have : 0 < g y := Ne.lt_of_le' hy (hg_nonneg y)
      rw [← hxyz]
      exact (lt_of_lt_of_le (by positivity) (hlb x y)).ne'

    have hh_supp_vol_pos : 0 < volume h.support :=
      calc
        0 < volume f.support :=
          pos_meas_supp_of_essSup_ne0 hf_essSup_ne0
        _ ≤ volume (f.support + g.support) :=
          meas_le_meas_add_right _ _
            (nonempty_of_measure_ne_zero
              (pos_meas_supp_of_essSup_ne0 hg_essSup_ne0).ne')
        _ ≤ volume h.support := measure_mono hfgh_supp_rel

    let A := {y : (ℝn 1) | h_essSup < h y}

    rcases lt_trichotomy h_essSup 0
      with hh_essSup_neg | hh_essSup_0 | hh_essSup_pos
    · have : A = univ := by sorry
      have : volume A > 0 := by sorry
      have : volume A = 0 := by
        unfold A h_essSup
        -- exact @meas_essSup_lt _ _ _ volume _ h _ _ _ (by isBoundedDefault)
        sorry
      sorry
    · sorry
    · exact hh_essSup_pos




  have superlevel_sets_meas_rel (l : ℝ) (hl_pos : 0 < l) :
    volume (superlevel_set f l) + volume (superlevel_set g l)
      ≤ volume (superlevel_set h l)
    := by
    let ϕ : ℝn 1 → ℝ := (MeasurableEquiv.funUnique (Fin 1) ℝ).toFun
    let A : Set ℝ := image ϕ (superlevel_set f l)
    let B : Set ℝ := image ϕ (superlevel_set g l)
    let C : Set ℝ := image ϕ (superlevel_set h l)

    have h := one_dim_BMInequality A B C

  -/




    -- exact one_dim_BMInequality
    --   (superlevel_set f l)

  -- let ϕ : ℝ → ℝn 1 := (MeasurableEquiv.funUnique (Fin 1) ℝ).invFun
  -- let f_iso : ℝ → ℝ := f ∘ ϕ
  -- let g_iso : ℝ → ℝ := f ∘ ϕ
  -- let h_iso : ℝ → ℝ := f ∘ ϕ


  have weighted_AM_GM_var (a b : ℝ) (ha_nonneg : 0 ≤ a) (hb_nonneg : 0 ≤ b) :
    a ^ (1 - t) * b ^ t ≤ (1 - t) ^ (1 - t) * t ^ t * (a + b)
    := by
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
