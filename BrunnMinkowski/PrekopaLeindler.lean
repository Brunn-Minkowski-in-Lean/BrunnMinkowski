import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import BrunnMinkowski.EuclideanSpace

open NNReal ENNReal MeasureTheory Finset
open Real Set MeasureTheory Filter Asymptotics

open scoped Real Topology

-- isomorhpism from any f.d. R-v.s. to R^d
#check toEuclidean

class IsEuclideanSpace
    (𝕜 : Type*) [TopologicalSpace 𝕜] [DivisionRing 𝕜]
    (α : Type*) [AddCommGroup α] [TopologicalSpace α] [TopologicalAddGroup α] [T2Space α]
    [Module 𝕜 α] [ContinuousSMul 𝕜 α] : Prop where
  finite_dimensional : FiniteDimensional 𝕜 α

namespace IsEuclideanSpace

variable {𝕜 : Type*} [TopologicalSpace 𝕜] [DivisionRing 𝕜]
variable {α : Type*} [AddCommGroup α] [TopologicalSpace α] [TopologicalAddGroup α] [T2Space α]
variable [Module 𝕜 α] [ContinuousSMul 𝕜 α]

instance {ι : Type*} [Fintype ι] : IsEuclideanSpace 𝕜 (EuclideanSpace 𝕜 ι) :=
  ⟨inferInstance⟩

instance {n : ℕ} : IsEuclideanSpace ℝ (EuclideanSpace ℝ (Fin n)) :=
  ⟨inferInstance⟩

end IsEuclideanSpace

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
    (hlb :
      ∀ x y : ℝn d,
      (f x)^(1 - t) * (g y)^t ≤ h (x + y)) :
  (∫ x, f x)^(1-t) * (∫ y, g y)^t ≤
  (1 - t)^(d * (1-t)) * t^(d*t) * (∫ x, h x)
  := by sorry
