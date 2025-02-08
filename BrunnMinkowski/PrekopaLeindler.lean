import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.RCLike.Basic
import BrunnMinkowski.EuclideanSpace
import Mathlib

open NNReal ENNReal MeasureTheory Finset
open Real Set MeasureTheory Filter Asymptotics

open scoped Real Topology

-- isomorhpism from any f.d. R-v.s. to R^d
#check toEuclidean

class EuclideanIsomorphismInvariant
    (P : (α : Type) → [AddCommGroup α] → [TopologicalSpace α] → [T2Space α] → [Module ℝ α] →
      [ContinuousSMul ℝ α] → [FiniteDimensional ℝ α] → Prop) :
    Prop where
  isomorphism_invariant
      (α : Type) [AddCommGroup α] [TopologicalSpace α] [T2Space α] [Module ℝ α]
        [ContinuousSMul ℝ α] [FiniteDimensional ℝ α]
      (β : Type) [AddCommGroup β] [TopologicalSpace β] [T2Space β] [Module ℝ β]
        [ContinuousSMul ℝ β] [FiniteDimensional ℝ β]
      (h : α ≃ₗ[ℝ] β) :
    P α ↔ P β

example {n : ℕ} : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n :=
  finrank_euclideanSpace_fin

-- TODO: Fix instance issues.
-- TODO: Consider higher order types if possible.
theorem EuclideanSpace.induction_on_finrank
    {P : (α : Type) → [AddCommGroup α] → [TopologicalSpace α] → [T2Space α] → [Module ℝ α] →
      [ContinuousSMul ℝ α] → [FiniteDimensional ℝ α] → Prop} [EuclideanIsomorphismInvariant P]
    {base0 : (α : Type) → [AddCommGroup α] → [TopologicalSpace α] → [T2Space α] → [Module ℝ α] →
      [ContinuousSMul ℝ α] → [FiniteDimensional ℝ α] → Module.finrank ℝ α = 0 → P α}
    {base1 : (α : Type) → [AddCommGroup α] → [TopologicalSpace α] → [T2Space α] → [Module ℝ α] →
      [ContinuousSMul ℝ α] → [FiniteDimensional ℝ α] → Module.finrank ℝ α = 1 → P α}
    {induct : {α : Type} → [AddCommGroup α] → [TopologicalSpace α] → [T2Space α] → [Module ℝ α] →
      [ContinuousSMul ℝ α] → [FiniteDimensional ℝ α] →
      {β : Type} → [AddCommGroup β] → [TopologicalSpace β] → [T2Space β] → [Module ℝ β] →
      [ContinuousSMul ℝ β] → [FiniteDimensional ℝ β] →
      P α → P β → P (α × β)}
    (α : Type) [AddCommGroup α] [TopologicalSpace α] [T2Space α] [Module ℝ α]
    [ContinuousSMul ℝ α] [FiniteDimensional ℝ α] : P α := by
  induction' h₀ : Module.finrank ℝ α using Nat.strong_induction_on generalizing α
  case h n ih _ _ _ _ _ _ =>
    match n with
    | 0 => exact base0 _ h₀
    | 1 => exact base1 _ h₀
    | n + 2 =>
      let eqv : α ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin (n + 1)) × EuclideanSpace ℝ (Fin 1)) :=
        sorry
      exact (‹EuclideanIsomorphismInvariant P›.isomorphism_invariant α _ eqv).mpr
        (induct
          (ih (n + 1) (by omega) _ finrank_euclideanSpace_fin)
          (ih 1 (by omega) _ finrank_euclideanSpace_fin))

theorem prekopa_leindler
    {t : ℝ} (h0t : 0 < t) (ht1 : t < 1)
    {d : ℕ} (f g h : ℝn d → ℝ)
    (hlb :
      ∀ x y : ℝn d,
      (f x)^(1 - t) * (g y)^t ≤ h (x + y)) :
  (∫ x, f x)^(1-t) * (∫ y, g y)^t ≤
  (1 - t)^(d * (1-t)) * t^(d*t) * (∫ x, h x)
  := by sorry
