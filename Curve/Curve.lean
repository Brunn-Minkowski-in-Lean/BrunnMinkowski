import Mathlib

structure Curve' (X : Type*) [TopologicalSpace X] where
  func : ℝ → X
  interval : Set ℝ
  isCompact_interval : IsCompact interval
  isConnected_interval : IsConnected interval
  nonempty_interval : interval.Nonempty
  func_continuousOn : ContinuousOn func interval

namespace Curve'

variable {X : Type*} [TopologicalSpace X]
variable {c : Curve' X}

protected noncomputable def lo (c : Curve' X) := sInf c.interval

protected noncomputable def hi (c : Curve' X) := sSup c.interval

@[simp]
theorem icc_lo_hi_eq_interval : Set.Icc c.lo c.hi = c.interval :=
  (eq_Icc_of_connected_compact c.isConnected_interval c.isCompact_interval).symm

protected def mk'
    (f : ℝ → X) (a b : ℝ) (h₁ : a ≤ b) (h₂ : ContinuousOn f (Set.Icc a b)) : Curve' X :=
  ⟨f, Set.Icc a b, isCompact_Icc, isConnected_Icc h₁, Set.nonempty_Icc.mpr h₁, h₂⟩

def IsClosed (c : Curve' X) : Prop :=
  c.func (sInf c.interval) = c.func (sSup c.interval)

def IsSimple (c : Curve' X) : Prop :=
  Set.InjOn c.func c.interval

def IsArc (c : Curve' X) : Prop :=
  c.func c.lo ≠ c.func c.hi

def IsSimpleClosed (c : Curve' X) : Prop :=
  IsClosed c ∧ Set.InjOn c.func c.interval ∧ c.func c.lo = c.func c.hi

def IsSimpleArc (c : Curve' X) : Prop :=
  IsArc c ∧ Set.InjOn c.func c.interval

end Curve'

