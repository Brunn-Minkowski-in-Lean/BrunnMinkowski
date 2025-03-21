import Mathlib.Algebra.Group.Operations
import Mathlib.Analysis.Convex.Body
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.MeanInequalitiesPow
import BrunnMinkowski.EuclideanSpace
import Aesop

import LeanSearchClient

open scoped Pointwise NNReal

variable {I : Type} [Fintype I] {n : ℕ} {ngz : n ≠ 0} {l : Real} {l_le_one : l ≤ 1} {l_ge_zero : l ≥ 0}

noncomputable def ConvexBody.volume (A : ConvexBody (ℝI I)) : NNReal :=
  (MeasureTheory.volume (A : Set (ℝI I))).toNNReal

-- μ(A)^(n⁻¹) + μ(B)^(n⁻¹) ≤ μ(A+B)^(n⁻¹)
def brunn_minkowski (A B : ConvexBody (ℝn n)) :
    A.volume ^ (n⁻¹ : ℝ) + B.volume ^ (n⁻¹ : ℝ) ≤ (A + B).volume ^ (n⁻¹ : ℝ)
    := sorry

lemma lemma_inequality (x y : ℝ≥0) (l : ℝ) (l_ge_zero : l ≥ 0) (l_le_one : l ≤ 1):
  l * x + (1 - l) * y
  ≥ x^(l : ℝ) * y^(1-l)
  := by
    apply Real.geom_mean_le_arith_mean2_weighted
    . exact l_ge_zero
    . linarith only [l_le_one]
    . exact x.prop
    . exact y.prop
    . linarith

lemma power_cancel (a : NNReal) (n : ℕ) (h : n ≠ (0 : ℕ)) : (a ^ (n⁻¹ : ℝ)) ^ (n : ℝ) = a :=
  by rw [← NNReal.rpow_mul a (n⁻¹ : ℝ), inv_mul_cancel₀ (Nat.cast_ne_zero.mpr h), NNReal.rpow_one a]

theorem help (x y : ℝ) (x_nn : 0 ≤ x) (y_nn : 0 ≤ y) (hn : 1 < n) :
    x + y ≤ (x^(1/n : ℝ) + y^(1/n : ℝ))^(n : ℝ) := by
  let m : ℝ := 1/n
  let mn : m = 1/n := rfl
  let hm : 1 < m := by sorry
  let f := fun t : ℝ => t^m

  have h_convex : ConvexOn ℝ (Set.Ioi 0) f :=
    (StrictConvexOn.subset (strictConvexOn_rpow hm) Set.Ioi_subset_Ici_self sorry).convexOn

 -- Define the points and weights for Jensen's Inequality
  let a : Fin 2 → ℝ≥0 := ![⟨x,x_nn⟩, ⟨y,y_nn⟩]
  let μ : Fin 2 → ℝ := ![1/2, 1/2]

  have hμ_nonneg : ∀ i ∈ Finset.univ, 0 ≤ μ i := by
    intro i
    fin_cases i
    . simp [μ]
    . simp [μ]

  have hμ_sum : ∑ i, μ i = 1 := by simp [μ] ; norm_num

  have foo : ∀ i ∈ Finset.univ, a i ∈ Set.Ioi 0 := by
    sorry

  have h_jensen := ConvexOn.map_sum_le h_convex hμ_nonneg hμ_sum foo

  simp [μ, a, f] at h_jensen
  norm_num at h_jensen

  repeat rw [Real.rpow_inv_rpow] at h_jensen
  repeat rw [← Distrib.left_distrib] at h_jensen

  have zero_gt_two_pow_m : 0 < ((2 : ℝ) ^ m)  := by positivity

  rw [← mul_le_mul_left zero_gt_two_pow_m, ← Real.mul_rpow] at h_jensen
  simp at h_jensen

  rw [← mul_assoc] at h_jensen
  rw [← Real.rpow_neg_one 2, ← Real.rpow_add] at h_jensen
  have eee : m + -1 = m - 1 := by exact rfl
  rw [eee] at h_jensen

  have bar : 0 ≤ x := by exact x_nn
  have foo (a : ℝ) (anz : 0≤a) : 2 ^ (1/n - 1 : ℝ) * a ≤ a := by
    cases eq_or_gt_of_le anz with
    | inl h_eq_zero =>
      rw [h_eq_zero, mul_zero]
    | inr h_gt_zero =>
      have : (1/n : ℝ) - 1 ≤ 0 := by
        rw [sub_nonpos]
        apply div_le_one_of_le₀
        . exact Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (Nat.not_eq_zero_of_lt hn))
        . exact Nat.cast_nonneg' n

      rw [mul_comm, mul_le_iff_le_one_right]
      apply Real.rpow_le_one_of_one_le_of_nonpos
      . norm_cast
      . exact this
      . exact h_gt_zero

  have aaaaaa: (x + y : ℝ)^m ≤ (x:ℝ)^m + (y:ℝ)^m:= by
    calc
      (↑x + ↑y) ^ m ≤ (2 : ℝ) ^ (m - 1) * (↑x ^ m + ↑y ^ m) := h_jensen
      _ ≤ ↑x ^ m + ↑y ^ m := foo (↑x ^ m + ↑y ^ m) (by positivity)

  have x_plus_y_is_positive: 0 ≤ x+y := by exact Left.add_nonneg x_nn y_nn
  have x_plus_y_pow_m_is_positive: 0 ≤ (x+y)^m := by exact Real.rpow_nonneg x_plus_y_is_positive m
  have m_is_positive: 0 ≤ m := by exact Nat.one_div_cast_nonneg n
  have m_inv_is_positive: 0 ≤ m⁻¹ := by exact inv_nonneg_of_nonneg m_is_positive
  have m_is_not_zero: m ≠ 0 := by sorry

  have hello := @Real.rpow_le_rpow ((x + y : ℝ)^m) _ _ x_plus_y_pow_m_is_positive aaaaaa m_inv_is_positive
  rw [← Real.rpow_mul, ← div_eq_mul_inv, div_self m_is_not_zero, mn] at hello
  norm_num at hello
  ring_nf
  exact_mod_cast hello
  exact x_plus_y_is_positive


theorem mul_nonneg_from_scratch {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y :=
  by
    by_cases x_eq_zero : x = 0
    · rw [x_eq_zero, zero_mul]
    have x_pos : 0 < x := lt_of_le_of_ne hx (Ne.symm x_eq_zero)
    calc
      0 = x * 0 := by rw [mul_zero]
      _ ≤ x * y := by exact mul_le_mul_of_nonneg_left hy x_pos.le

-- μ(A)^λ μ(B)^(1-λ) ≤ μ(λA + (1-λ)B)
def brunn_minkowski_multiplicative (A B : ConvexBody (ℝn n)):
  A.volume^l • B.volume^(1-l)
  ≤ (l • A + (1 - l) • B).volume
  := by
  calc
    -- μ(A)^λ μ(B)^(1-λ) ≤ λμ(A) + (1-λ)μ(B)
    A.volume^l • B.volume^(1-l) ≤ l * A.volume + (1 - l) • B.volume :=
      lemma_inequality
        A.volume
        B.volume
        l
        l_ge_zero
        l_le_one

    -- λμ(A) + (1-λ)μ(B) ≤ {λμ(A)^(n⁻¹) + (1-λ)μ(B)^(n⁻¹)}^n
    _ ≤ ((l * A.volume) ^ (n⁻¹ : ℝ) + ((1 - l) * B.volume) ^ (n⁻¹ : ℝ))^(n : ℝ) := by
      if n_is_one : n = 1 then
        have foo :
          (l * A.volume) + ((1 - l) * B.volume) ≤
          ((l * A.volume)^(1/n : ℝ) + ((1 - l) * B.volume)^(1/n : ℝ))^(n) := by
            simp [n_is_one]
        field_simp
        norm_cast
      else
        have a_nn : 0 ≤ (l * A.volume.val) := mul_nonneg_from_scratch l_ge_zero A.volume.prop
        have b_nn : 0 ≤ ((1 - l) * B.volume) := mul_nonneg_from_scratch (sub_nonneg_of_le l_le_one) B.volume.prop

        have bar : 1 < n := by
          cases n with
            | zero => contradiction
            | succ n' =>
              cases n' with
              | zero => contradiction
              | succ _ => exact Nat.succ_lt_succ (Nat.zero_lt_succ _)

        have foo := help (l * A.volume) ((1 - l) * B.volume) a_nn b_nn bar
        norm_num at foo

        norm_cast
    _ ≤ ((l • A).volume ^ (n⁻¹ : ℝ) + ((1 - l) • B).volume ^ (n⁻¹ : ℝ))^(n : ℝ) := by sorry

    _ ≤ (l • A + (1 - l) • B).volume := by
      rw [← power_cancel ((l• A + (1 - l) • B).volume) n ngz]
      apply NNReal.rpow_le_rpow (@brunn_minkowski n (l • A) ((1 - l) • B)) (Nat.cast_nonneg' n)
