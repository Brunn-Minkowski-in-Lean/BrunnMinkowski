import Mathlib.Algebra.Group.Operations
import Mathlib.Analysis.Convex.Body
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.MeanInequalitiesPow
import BrunnMinkowski.EuclideanSpace

import LeanSearchClient

#leansearch "exponential is convex."
#leansearch "Jansen's inequality two variable form."

#check NNReal.rpow_add_le_add_rpow

open scoped Pointwise NNReal

variable {I : Type} [Fintype I] {n : ℕ} {ngz : n ≠ 0} {l : Set.Icc (0 : ℝ) (1 : ℝ)}

noncomputable def ConvexBody.volume (A : ConvexBody (ℝI I)) : NNReal :=
  (MeasureTheory.volume (A : Set (ℝI I))).toNNReal

-- μ(A)^(n⁻¹) + μ(B)^(n⁻¹) ≤ μ(A+B)^(n⁻¹)
def brunn_minkowski (A B : ConvexBody (ℝn n)) :
    A.volume ^ (n⁻¹ : ℝ) + B.volume ^ (n⁻¹ : ℝ) ≤ (A + B).volume ^ (n⁻¹ : ℝ)
    := sorry

lemma lemma_inequality (x y : ℝ≥0) (l : Set.Icc (0 : ℝ) (1 : ℝ)):
  l.1 * x + (1 - l.1) * y
  ≥ x^(l : ℝ) * y^(1-l.1)
  := by
    apply Real.geom_mean_le_arith_mean2_weighted
    . exact l.2.1
    . linarith only [l.2.2]
    . exact x.prop
    . exact y.prop
    . linarith

lemma power_cancel (a : NNReal) (n : ℕ) (h : n ≠ (0 : ℕ)) : (a ^ (n⁻¹ : ℝ)) ^ (n : ℝ) = a :=
  by rw [← NNReal.rpow_mul a (n⁻¹ : ℝ), inv_mul_cancel₀ (Nat.cast_ne_zero.mpr h), NNReal.rpow_one a]

theorem help (x y : NNReal) (n : ℕ) (hn : 1 < n) :
    x + y ≤ (x^(1/n : ℝ) + y^(1/n : ℝ))^(n : ℝ) := by
  let m := 1/n
  let mn : m = 1/n := by exact rfl
  let hm : 1 < m := by sorry
  let f := fun t : ℝ => t^(m : ℝ)

  have h_convex : ConvexOn ℝ (Set.Ioi 0) f :=
    (StrictConvexOn.subset (strictConvexOn_rpow (Nat.one_lt_cast.mpr hm)) Set.Ioi_subset_Ici_self sorry).convexOn

 -- Define the points and weights for Jensen's Inequality
  let a : Fin 2 → ℝ≥0 := ![x, y]
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

  have bbb : 0 < ((2 : ℝ) ^ m)  := by positivity

  rw [← mul_le_mul_left bbb, ← mul_pow] at h_jensen
  simp [mul_assoc] at h_jensen
  rw [mn] at h_jensen
  rw []

  have h_mul : 0 < (2 : ℝ≥0) ^ n := sorry

  have : ∀ {x y : ℝ≥0} {z : ℝ}, 0 < z → (x ^ z ≤ y ^ z ↔ x ≤ y) := NNReal.rpow_le_rpow_iff

  #check Real.rpow_le_rpow_iff



  #check mul_le_mul_left



-- μ(A)^λ μ(B)^(1-λ) ≤ μ(λA + (1-λ)B)
def brunn_minkowski_multiplicative (A B : ConvexBody (ℝn n)):
  A.volume^l.1 • B.volume^(1-l.1)
  ≤ (l.1 • A + (1 - l.1) • B).volume
  := by
--  have foo : (l.1 • A).volume = l.1 * A.volume := by exact?

  -- (μ(λA)^(n⁻¹) + μ((1-λ)B)^(n⁻¹))^n ≤ μ(λA + (1-λ)B)
  have right_side:
      ((l.1 • A).volume ^ (n⁻¹ : ℝ) + ((1 - l.1) • B).volume ^ (n⁻¹ : ℝ)) ^ (n : ℝ)
      ≤ (l.1 • A + (1 - l.1) • B).volume
       := by
          rw [← power_cancel ((l.1 • A + (1 - l.1) • B).volume) n ngz]
          apply NNReal.rpow_le_rpow (@brunn_minkowski n (l.1 • A) ((1 - l.1) • B)) (Nat.cast_nonneg' n)

  calc
    -- μ(A)^λ μ(B)^(1-λ) ≤ λμ(A) + (1-λ)μ(B)
    A.volume^l.1 • B.volume^(1-l.1) ≤ l.1 * A.volume + (1 - l.1) • B.volume := lemma_inequality A.volume B.volume l

    -- λμ(A) + (1-λ)μ(B) ≤ {λμ(A)^(n⁻¹) + (1-λ)μ(B)^(n⁻¹)}^n
    _ ≤ ((l.1 * A.volume) ^ (n⁻¹ : ℝ) + ((1 - l.1) * B.volume) ^ (n⁻¹ : ℝ))^(n : ℝ) := by sorry

    _ = ((l.1 • A).volume ^ (n⁻¹ : ℝ) + ((1 - l.1) • B).volume ^ (n⁻¹ : ℝ))^(n : ℝ) := by sorry

    _ ≤ (l.1 • A + (1 - l.1) • B).volume := by
      rw [← power_cancel ((l.1 • A + (1 - l.1) • B).volume) n ngz]
      apply NNReal.rpow_le_rpow (@brunn_minkowski n (l.1 • A) ((1 - l.1) • B)) (Nat.cast_nonneg' n)



/-
  -- μ(λA)^(n⁻¹) + μ((1-λ)B)^(n⁻¹) ≤ (μ(λA)^(n⁻¹) + μ((1-λ)B)^(n⁻¹))^n

-- (μ(λA)^(n⁻¹) + μ((1-λ)B)^(n⁻¹))^n ≥ μ(A)^λ μ(B)^(1-λ)
  have left_side:
      ((l.1 • A).volume ^ (n⁻¹ : ℝ) + ((1 - l.1) • B).volume ^ (n⁻¹ : ℝ))^(n : ℝ)
      ≥ A.volume ^ l.1 • B.volume ^ (1 - l.1)
       := sorry

  -- λμ(A) + (1-λ)μ(B) ≥ μ(A)^λ * μ(B)^(1-λ)
  have foo : l.1 * A.volume + (1 - l.1) • B.volume ≥ A.volume ^ (l : ℝ) * B.volume ^ (1 - l.1):= lemma_inequality A.volume B.volume l


  /-have ccc :
    (((A.volume ^ (l : ℝ)) ^ ↑n) ^ (n⁻¹ : ℝ) + ((B.volume ^ (1 - l : ℝ)) ^ ↑n) ^ (n⁻¹ : ℝ)) ^ (n : ℝ)
    ≥ ((A.volume ^ (l : ℝ) + B.volume ^ (1 - l : ℝ)) ^ ↑n)
    := by
      have ddd := @NNReal.rpow_le_rpow_iff (((A.volume ^ (l : ℝ)) ^ ↑n) ^ (n⁻¹ : ℝ) + ((B.volume ^ (1 - l : ℝ)) ^ ↑n) ^ (n⁻¹ : ℝ)) ((A.volume ^ (l : ℝ) + B.volume ^ (1 - l : ℝ)) ^ ↑n) n (Nat.cast_pos'.mpr (Nat.pos_of_ne_zero ngz))
      have eee := bbb
      sorry

    #check NNReal.rpow_le_rpow_iff-/



  have bar :
    ((l.1 • A).volume ^ (n⁻¹ : ℝ) + ((1 - l.1) • B).volume ^ (n⁻¹ : ℝ))^(n : ℝ)
    ≥ l.1 * A.volume + (1 - l.1) • B.volume := by sorry



  calc
    right_side
-/
