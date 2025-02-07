import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import BrunnMinkowski.EuclideanSpace
import BrunnMinkowski.OneDim

open NNReal ENNReal MeasureTheory Finset
open Real Set MeasureTheory Filter Asymptotics

open scoped Real Topology

open Pointwise

-- isomorhpism from any f.d. R-v.s. to R^d
#check toEuclidean

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

noncomputable def superlevel_set (f : ℝn n → ℝ) (c : ℝ) : Set (ℝn n)
  := {x | c < f x}

lemma measurable_ray {c : ℝ} : MeasurableSet {y | c < y} :=
  measurableSet_Ioi

lemma measurable_superlevel_set_of_measurable
    {f : ℝn n → ℝ} {hf_measurable : Measurable f}
    {c : ℝ} :
  MeasurableSet (superlevel_set f c)
  := by
  have measurable_ray_c : MeasurableSet {y | c < y} := measurable_ray
  rw [superlevel_set]
  -- 'measurability' can replace the below lines
  simp_all only [measurableSet_setOf]
  exact Measurable.comp' measurable_ray_c hf_measurable

lemma nonneg_integrable_integral_eq_integral_superlevel_set_meas
    {f : ℝn n → ℝ} (hf_nonneg : 0 ≤ f) (hf_integrable : Integrable f) :
  (∫ x, f x) = (∫ y, (fun l ↦ (volume (superlevel_set f l)).toReal) y)
  := by
  sorry

lemma prekopa_leindler_dim1
    {t : ℝ} (h0t : 0 < t) (ht1 : t < 1)
    (f g h : ℝn 1 → ℝ)
    (hf_nonneg : 0 ≤ f) (hf_integrable : Integrable f)
    (hg_nonneg : 0 ≤ g) (hg_integrable : Integrable g)
    (hh_nonneg : 0 ≤ h) (hh_integrable : Integrable h)
    (hlb :
      ∀ x y : ℝn 1,
      (f x)^(1 - t) * (g y)^t ≤ h (x + y)) :
  (∫ x, f x) ^ (1 - t) * (∫ y, g y) ^ t ≤ (1 - t) ^ (1 - t) * t ^ t * (∫ x, h x)
  := by

  have one_sub_t_pos : 0 < 1 - t := sub_pos.mpr ht1
  have t_nonneg : 0 ≤ t := le_of_lt h0t

  have superlevel_sets_rel (l : ℝ) (hl_pos : 0 < l) :
    superlevel_set f l + superlevel_set g l ⊆ superlevel_set h l
    := by
    refine Set.add_subset_iff.mpr ?_
    intro x hx y hy
    rw [superlevel_set, mem_setOf_eq] at *
    calc
      l = l ^ (1 - t) * l ^ t := by
        rw [← rpow_add hl_pos, sub_add_cancel, rpow_one l]
      _ < (f x) ^ (1 - t) * (g y) ^ t := by gcongr
      _ ≤ h (x + y) := by exact hlb x y

  have superlevel_sets_meas_rel (l : ℝ) (hl_pos : 0 < l) :
    volume (superlevel_set f l) + volume (superlevel_set g l)
      ≤ volume (superlevel_set h l)
    := by
    sorry
    -- exact one_dim_BMInequality
    --   (superlevel_set f l)

  have integral_rel : (∫ x, f x) + (∫ x, g x) ≤ (∫ x, h x) := by sorry

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
        · exact ne_of_gt h0t
        · exact ne_of_gt one_sub_t_pos

  apply le_trans
    ( weighted_AM_GM_var (∫ x, f x) (∫ x, g x)
      (integral_nonneg hf_nonneg) (integral_nonneg hg_nonneg) )
  gcongr
