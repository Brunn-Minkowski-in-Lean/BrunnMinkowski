import Mathlib.Algebra.Group.Operations
import Mathlib.Analysis.Convex.Body
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import BrunnMinkowski.EuclideanSpace

open scoped Pointwise NNReal

variable {I : Type} [Fintype I] {n : ℕ} {l : Set.Icc (0 : ℝ) (1 : ℝ)}

noncomputable def ConvexBody.volume (A : ConvexBody (ℝI I)) : ENNReal :=
  MeasureTheory.volume (A : Set (ℝI I))

-- μ(A)^(n⁻¹) + μ(B)^(n⁻¹) ≤ μ(A+B)^(n⁻¹)
def brunn_minkowski (A B : ConvexBody (ℝn n)) :
    A.volume ^ (n⁻¹ : ℝ) + B.volume ^ (n⁻¹ : ℝ) ≤ (A + B).volume ^ (n⁻¹ : ℝ)
    := sorry

-- μ(λA + (1-λ)B) ≥ μ(A)^λ μ(B)^(1-λ)
def brunn_minkowski_multiplicative (A B : ConvexBody (ℝn n)):
  A.volume^(l : ℝ) • B.volume^(1-(l : ℝ)) ≤ ((l : ℝ) • A + (1 - (l : ℝ)) • B).volume
  := sorry
