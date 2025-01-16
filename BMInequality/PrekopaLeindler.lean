import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

open NNReal ENNReal MeasureTheory Finset
open Real Set MeasureTheory Filter Asymptotics

open scoped Real Topology

theorem ineqPrekopaLeindler
    {t : ℝ} (h0t : 0 < t) (ht1 : t < 1)
    {d : ℕ} (f g h : EuclideanSpace ℝ (Fin d) → ℝ)
    (hlb :
      ∀ x y : EuclideanSpace ℝ (Fin d),
      (f x)^(1 - t) * (g y)^t ≤ h (x + y)) :
  (∫ x, f x)^(1-t) * (∫ y, g y)^t ≤
  (1 - t)^(d * (1-t)) * t^(d*t) * (∫ x, h x)
  := by sorry
