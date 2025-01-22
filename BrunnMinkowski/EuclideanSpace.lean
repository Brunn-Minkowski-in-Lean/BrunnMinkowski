import Mathlib.Analysis.Convex.Body
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder

open scoped Pointwise NNReal

variable {I : Type} [Fintype I] {n : ℕ}
-- `I` is the index set for the basis
abbrev ℝI (I : Type) : Type := EuclideanSpace ℝ I
-- canonical choice `I = Fin n = {0, 1, ..., n-1}`
abbrev ℝn (n : ℕ) : Type := ℝI (Fin n)
