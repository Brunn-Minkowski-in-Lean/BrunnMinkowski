import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.RCLike.Basic
import BrunnMinkowski.EuclideanSpace

open NNReal ENNReal MeasureTheory Finset
open Real Set MeasureTheory Filter Asymptotics

open scoped Real Topology

-- isomorhpism from any f.d. R-v.s. to R^d
#check toEuclidean

class EuclideanBaseStructure (α : Type*) extends
  AddCommGroup α,
  TopologicalSpace α,
  T2Space α,
  Module ℝ α,
  ContinuousSMul ℝ α,
  FiniteDimensional ℝ α

instance {α : Type} [EuclideanBaseStructure α] {β : Type} [EuclideanBaseStructure β] :
    EuclideanBaseStructure (α × β) :=
  sorry

instance {n : ℕ} : EuclideanBaseStructure (EuclideanSpace ℝ (Fin n)) :=
  sorry

class EuclideanIsoInvariant (P : (α : Type) → [EuclideanBaseStructure α] → Prop) : Prop where
  isomorphism_invariant
      (α : Type) [EuclideanBaseStructure α] (β : Type) [EuclideanBaseStructure β] (h : α ≃ₗ[ℝ] β) :
    P α ↔ P β

lemma asdf {n : ℕ} : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n :=
  finrank_euclideanSpace_fin

-- TODO: Fix instance issues.
-- TODO: Consider higher order types if possible.
theorem EuclideanSpace.induction_on_finrank
    {P : (α : Type) → [EuclideanBaseStructure α] → Prop} [EuclideanIsoInvariant P]
    {base0 : (α : Type) → [EuclideanBaseStructure α] → Module.finrank ℝ α = 0 → P α}
    {base1 : (α : Type) → [EuclideanBaseStructure α] → Module.finrank ℝ α = 1 → P α}
    {induct : {α : Type} → [EuclideanBaseStructure α] → {β : Type} → [EuclideanBaseStructure β] →
      P α → P β → P (α × β)}
    (α : Type) [EuclideanBaseStructure α] : P α := by
  induction' h₀ : Module.finrank ℝ α using Nat.strong_induction_on generalizing α
  case h n ih _ =>
    match n with
    | 0 => exact base0 _ h₀
    | 1 => exact base1 _ h₀
    | n + 2 =>
      refine (‹EuclideanIsoInvariant P›.isomorphism_invariant α
          ((EuclideanSpace ℝ (Fin (n + 1))) × (EuclideanSpace ℝ (Fin 1))) ?_).mpr
        (induct
          (ih (n + 1) (by omega) (EuclideanSpace ℝ (Fin (n + 1))) ?_)
          (ih 1 (by omega) _ ?_))
      · sorry
      · sorry -- exact @finrank_euclideanSpace_fin ℝ _ (n + 1)
      · sorry -- exact finrank_euclideanSpace_fin

theorem prekopa_leindler
    {t : ℝ} (h0t : 0 < t) (ht1 : t < 1)
    {d : ℕ} (f g h : ℝn d → ℝ)
    (hlb :
      ∀ x y : ℝn d,
      (f x)^(1 - t) * (g y)^t ≤ h (x + y)) :
  (∫ x, f x)^(1-t) * (∫ y, g y)^t ≤
  (1 - t)^(d * (1-t)) * t^(d*t) * (∫ x, h x)
  := by sorry
