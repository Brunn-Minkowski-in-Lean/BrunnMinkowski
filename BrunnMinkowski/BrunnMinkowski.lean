import Mathlib.Algebra.Group.Operations
import Mathlib.Analysis.Convex.Body
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import BrunnMinkowski.EuclideanSpace

import LeanSearchClient

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

-- μ(λA + (1-λ)B) ≥ μ(A)^λ μ(B)^(1-λ)
def brunn_minkowski_multiplicative (A B : ConvexBody (ℝn n)):
  (l.1 • A + (1 - l.1) • B).volume ≥ A.volume^(l : ℝ) • B.volume^(1-l.1)
  := by
  -- μ(λA + (1-λ)B) ≥ (μ(λA)^(n⁻¹) + μ((1-λ)B)^(n⁻¹))^n
  have right_side:
       (l.1 • A + (1 - l.1) • B).volume
        ≥ ((l.1 • A).volume ^ (n⁻¹ : ℝ) + ((1 - l.1) • B).volume ^ (n⁻¹ : ℝ)) ^ (n : ℝ)
       := by
          rw [← power_cancel ((l.1 • A + (1 - l.1) • B).volume) n ngz]
          apply NNReal.rpow_le_rpow (@brunn_minkowski n (l.1 • A) ((1 - l.1) • B)) (Nat.cast_nonneg' n)

  have aaa :
    ((l.1 • A).volume ^ (n⁻¹ : ℝ) + ((1 - l.1) • B).volume ^ (n⁻¹ : ℝ)) ^ (n : ℝ)
    ≥ (l.1 • A).volume + ((1 - l.1) • B).volume
    := by sorry

  have bbb :
    ((A.volume ^ (l : ℝ)) ^ ↑n) ^ (n⁻¹ : ℝ) + ((B.volume ^ (1 - l : ℝ)) ^ ↑n) ^ (n⁻¹ : ℝ)
    ≥ ((A.volume ^ (l : ℝ) + B.volume ^ (1 - l : ℝ)) ^ ↑n) ^ (n⁻¹ : ℝ)
    := by
      have hello : 1 ≤ n := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr ngz)
      --have world : 1 ≤ (n⁻¹ : ℝ) :=

      #check ENNReal.inv_le_one


      have minkowski_lp :=
        @NNReal.Lp_add_le
          ℕ
          (singleton 0)
          (λ _ => A.volume ^ (l : ℝ) ^ (n⁻¹ : ℝ))
          (λ _ => B.volume ^ (1 - l.1) ^ (n⁻¹ : ℝ))
          (n : ℝ)
          (Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr ngz))

      have aa := by
        have cat :=
          @NNReal.rpow_self_rpow_inv
            n
             (Nat.cast_ne_zero.mpr ngz) ((A.volume ^ (l : ℝ) ^ (n⁻¹ : ℝ) + B.volume ^ (1 - l : ℝ ) ^ (n⁻¹ : ℝ)))
        conv at cat =>
          lhs
          rw [div_eq_inv_mul 1 (n : ℝ)]

        exact cat


      conv at minkowski_lp =>
        congr
        . simp
          rw [← aa]
        . simp


      sorry -- exact minkowski_lp

  have ccc :
    (((A.volume ^ (l : ℝ)) ^ ↑n) ^ (n⁻¹ : ℝ) + ((B.volume ^ (1 - l : ℝ)) ^ ↑n) ^ (n⁻¹ : ℝ)) ^ (n : ℝ)
    ≥ ((A.volume ^ (l : ℝ) + B.volume ^ (1 - l : ℝ)) ^ ↑n)
    := by
      have ddd := @NNReal.rpow_le_rpow_iff (((A.volume ^ (l : ℝ)) ^ ↑n) ^ (n⁻¹ : ℝ) + ((B.volume ^ (1 - l : ℝ)) ^ ↑n) ^ (n⁻¹ : ℝ)) ((A.volume ^ (l : ℝ) + B.volume ^ (1 - l : ℝ)) ^ ↑n) n (Nat.cast_pos'.mpr (Nat.pos_of_ne_zero ngz))
      have eee := bbb
      sorry

    #check NNReal.rpow_le_rpow_iff

  -- λμ(A) + (1-λ)μ(B) ≥ μ(A)^λ * μ(B)^(1-λ)
  have foo : l.1 * A.volume + (1 - l.1) • B.volume ≥ A.volume ^ (l : ℝ) * B.volume ^ (1 - l.1):= lemma_inequality A.volume B.volume l

  have bar :
    ((l.1 • A).volume ^ (n⁻¹ : ℝ) + ((1 - l.1) • B).volume ^ (n⁻¹ : ℝ))^(n : ℝ)
    ≥ l.1 * A.volume + (1 - l.1) • B.volume := by sorry

  -- (μ(λA)^(n⁻¹) + μ((1-λ)B)^(n⁻¹))^n ≥ μ(A)^λ μ(B)^(1-λ)
  have left_side:
      ((l.1 • A).volume ^ (n⁻¹ : ℝ) + ((1 - l.1) • B).volume ^ (n⁻¹ : ℝ))^(n : ℝ)
      ≥ A.volume ^ l.1 • B.volume ^ (1 - l.1)
       := sorry

  calc
    right_side

  sorry

/-    -- ⊢ a * (b * c) = a * (c * b)
    lhs
    -- ⊢ a * (b * c)
    arg 2
    -- ⊢ b * c
    rw [Nat.mul_comm]  -/

def foo : Finset NNReal := singleton 5

#check Finset.sum_range

#check λ (_ : ℕ) => 10

#leansearch "how to lift Natural number to real number?"

#check (⟨l, l.2.1⟩ : NNReal)


variable {A : ConvexBody (ℝn n)}

#check Nat.not_eq_zero_of_lt

#check unitInterval.nonneg'
