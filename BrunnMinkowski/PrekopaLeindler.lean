import Mathlib

namespace EuclideanSpace

def EuclideanProd
    (α : Type*) [AddCommGroup α] [TopologicalSpace α] [IsTopologicalAddGroup α] [T2Space α]
    [Module ℝ α] [ContinuousSMul ℝ α] [FiniteDimensional ℝ α]
    (β : Type*) [AddCommGroup β] [TopologicalSpace β] [IsTopologicalAddGroup β] [T2Space β]
    [Module ℝ β] [ContinuousSMul ℝ β] [FiniteDimensional ℝ β] :=
  WithLp 2 (α × β)

infixl:35 " ×ₑ " => EuclideanProd

section

variable {α : Type*} [AddCommGroup α] [TopologicalSpace α] [IsTopologicalAddGroup α] [T2Space α]
variable [Module ℝ α] [ContinuousSMul ℝ α] [FiniteDimensional ℝ α]

end

section EuclideanProd

variable {α : Type*} [AddCommGroup α] [TopologicalSpace α] [IsTopologicalAddGroup α] [T2Space α]
variable [Module ℝ α] [ContinuousSMul ℝ α] [FiniteDimensional ℝ α]
variable {β : Type*} [AddCommGroup β] [TopologicalSpace β] [IsTopologicalAddGroup β] [T2Space β]
variable [Module ℝ β] [ContinuousSMul ℝ β] [FiniteDimensional ℝ β]

instance : AddCommGroup (α ×ₑ β) :=
  WithLp.instAddCommGroup 2 _

instance : TopologicalSpace (α ×ₑ β) :=
  WithLp.instProdTopologicalSpace 2 _ _

instance : IsTopologicalAddGroup (α ×ₑ β) :=
  Prod.instIsTopologicalAddGroup

instance : T0Space (α ×ₑ β) :=
  Prod.instT0Space

instance : R1Space (α ×ₑ β) :=
  instR1SpaceProd

instance : T2Space (α ×ₑ β) :=
  instT2SpaceOfR1SpaceOfT0Space

instance : Module ℝ (α ×ₑ β) :=
  Prod.instModule

instance : ContinuousSMul ℝ (α ×ₑ β) :=
  Prod.continuousSMul

instance : FiniteDimensional ℝ (α ×ₑ β) :=
  WithLp.instModuleFinite 2 _ _

instance : MeasurableSpace (α ×ₑ β) :=
  borel (α ×ₑ β)

instance : BorelSpace (α ×ₑ β) :=
  ⟨rfl⟩

end EuclideanProd

end EuclideanSpace

section

open MeasureTheory

set_option linter.unusedVariables false in
def PrekopaLeindler.Condition
    {t : ℝ} (ht₁ : 0 < t) (ht₂ : t < 1) {ι : Type*} [Fintype ι]
    (f : EuclideanSpace ℝ ι → ℝ) (hf₁ : Integrable f) (hf₂ : ∀ x, 0 ≤ f x)
    (g : EuclideanSpace ℝ ι → ℝ) (hg₁ : Integrable g) (hg₂ : ∀ x, 0 ≤ g x)
    (h : EuclideanSpace ℝ ι → ℝ) (hh₁ : Integrable h) : Prop :=
  ∀ x y : EuclideanSpace ℝ ι, (f x) ^ (1 - t) * (g y) ^ t ≤ h (x + y)

theorem PrekopaLeindler.statement
    {t : ℝ} (ht₁ : 0 < t) (ht₂ : t < 1)
    {ι : Type*} [Fintype ι]
    (hι : ∀ ⦃f : EuclideanSpace ℝ ι → ℝ⦄ hf₁ hf₂ ⦃g⦄ hg₁ hg₂ ⦃h⦄ hh₁,
      PrekopaLeindler.Condition ht₁ ht₂ f hf₁ hf₂ g hg₁ hg₂ h hh₁ →
      ∀ ) : True :=
  sorry
    
namespace PrekopaLeindler

variable {t : ℝ} (ht₁ : 0 < t) (ht₂ : t < 1)
variable {ι : Type*} [Fintype ι]
variable {f : EuclideanSpace ℝ ι → ℝ} (hf₁ : Integrable f) (hf₂ : ∀ x, 0 ≤ f x)
variable {g : EuclideanSpace ℝ ι → ℝ} (hg₁ : Integrable g) (hg₂ : ∀ x, 0 ≤ g x)
variable {h : EuclideanSpace ℝ ι → ℝ} (hh₁ : Integrable h)

theorem Condition.nonnegative
    (h₀ : Condition ht₁ ht₂ f hf₁ hf₂ g hg₁ hg₂ h hh₁) {x : EuclideanSpace ℝ ι} :
    0 ≤ h x := by
  have := h₀ x 0; rw [add_zero] at this; refine le_trans ?_ this
  have := hf₂ x; have := hg₂ 0; positivity

end PrekopaLeindler

-- TODO: Add PrekopaLeindler.Statement

end

