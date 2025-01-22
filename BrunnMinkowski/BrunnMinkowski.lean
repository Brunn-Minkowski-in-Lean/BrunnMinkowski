import Mathlib.Analysis.Convex.Body
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import BrunnMinkowski.EuclideanSpace

open scoped Pointwise NNReal

noncomputable def ConvexBody.volume (A : ConvexBody (ℝI I)) : ENNReal :=
  MeasureTheory.volume (A : Set (ℝI I))

def brunn_minkowski (A B : ConvexBody (ℝn n)) :
    A.volume ^ (n⁻¹ : ℝ) + B.volume ^ (n⁻¹ : ℝ) ≤
    (A + B).volume ^ (n⁻¹ : ℝ) := by
  sorry
