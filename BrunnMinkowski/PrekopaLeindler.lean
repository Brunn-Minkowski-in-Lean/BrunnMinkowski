import Mathlib

namespace EuclideanSpace

def EuclideanProd
    (α : Type*) [AddCommGroup α] [TopologicalSpace α] [IsTopologicalAddGroup α] [T2Space α]
    [Module ℝ α] [ContinuousSMul ℝ α] [FiniteDimensional ℝ α]
    (β : Type*) [AddCommGroup β] [TopologicalSpace β] [IsTopologicalAddGroup β] [T2Space β]
    [Module ℝ β] [ContinuousSMul ℝ β] [FiniteDimensional ℝ β] :=
  WithLp 2 (α × β)

infixl:35 " ×ₑ " => EuclideanProd

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

noncomputable instance : MeasurableSpace (α ×ₑ β) :=
  EuclideanSpace.instMeasurableSpaceReal (toEuclidean (α ×ₑ β))

end EuclideanProd

end EuclideanSpace

