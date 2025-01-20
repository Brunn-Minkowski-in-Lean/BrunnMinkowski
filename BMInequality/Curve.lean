import Mathlib

structure Curve' (X : Type*) [TopologicalSpace X] where
  func : ℝ → X
  interval : Set ℝ
  interval_is_connected : IsConnected interval
  interval_is_compact : IsCompact interval
  interval_is_nonempty : interval.Nonempty
  func_is_continuous : ContinuousOn func (Set.Icc 0 1)

namespace Curve'

variable {X : Type*} [TopologicalSpace X]

class Closed (c : Curve' X) : Prop where
  isClosed : c.func (sInf c.interval) = c.func (sSup c.interval)

class Simple (c : Curve' X) : Prop where
  isSimple : Set.InjOn c.func c.interval

class Arc (c : Curve' X) : Prop where
  isArc : c.func 0 ≠ c.func 1

class SimpleClosed (c : Curve' X) extends Closed c : Prop where
  isSimple : Set.InjOn c.func (Set.Ico 0 1) ∧ c.func 0 = c.func 1

class SimpleArc (c : Curve' X) extends Arc c : Prop where
  isSimple : Set.InjOn c.func (Set.Icc 0 1)

def ProperlyEquiv (c₁ c₂ : Curve' X) : Prop :=
  ∃ f : ℝ → ℝ,
    StrictMonoOn f c₂.interval ∧
    ContinuousOn f c₂.interval ∧
    c₁.func (f (sInf c₁.interval)) = c₂.func (sInf c₂.interval) ∧
    c₁.func (f (sSup c₁.interval)) = c₂.func (sSup c₂.interval) ∧
    ∀ t ∈ c₂.interval, c₂.func t = c₁.func (f t)

def ImproperlyEquiv (c₁ c₂ : Curve' X) : Prop :=
  ∃ f : ℝ → ℝ,
    StrictAntiOn f c₂.interval ∧
    ContinuousOn f c₂.interval ∧
    c₁.func (f (sSup c₁.interval)) = c₂.func (sInf c₂.interval) ∧
    c₁.func (f (sInf c₁.interval)) = c₂.func (sSup c₂.interval) ∧
    ∀ t ∈ c₂.interval, c₂.func t = c₁.func (f t)

instance isSetoid : Setoid (Curve' X) where
  r c₁ c₂ := ProperlyEquiv c₁ c₂ ∨ ImproperlyEquiv c₁ c₂
  iseqv :=
   ⟨fun _ ↦ .inl ⟨id, strictMonoOn_id, continuousOn_id, rfl, rfl, fun _ _ ↦ rfl⟩,
    fun h ↦ by
      rcases h with h | h
      · sorry
      · sorry,
    fun h₁ h₂ ↦ by
      rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
      · sorry
      · sorry
      · sorry
      · sorry⟩

def rel_def (c₁ c₂ : Curve' X) : c₁ ≈ c₂ ↔ ProperlyEquiv c₁ c₂ ∨ ImproperlyEquiv c₁ c₂ :=
  ⟨id, id⟩

end Curve'

def Curve (X : Type*) [TopologicalSpace X] :=
  Quotient (@Curve'.isSetoid X _)

namespace Curve

variable {X : Type*} [TopologicalSpace X]
variable {c c₁ c₂ c₃ : Curve X}

instance : Coe (Curve' X) (Curve X) :=
  ⟨Quot.mk _⟩

end Curve

