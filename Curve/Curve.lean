import Mathlib

structure Curve' (X : Type*) [TopologicalSpace X] where
  func : ℝ → X
  interval : Set ℝ
  isConnected_interval : IsConnected interval
  nonempty_interval : interval.Nonempty
  func_continuousOn : ContinuousOn func interval

structure Path' (X : Type*) [TopologicalSpace X] extends Curve' X where
  isCompact_interval : IsCompact interval

namespace Path'

variable {X : Type*} [TopologicalSpace X]
variable {c c₁ c₂ : Path' X}

protected noncomputable def lo (c : Path' X) : ℝ :=
  sInf c.interval

protected noncomputable def hi (c : Path' X) : ℝ :=
  sSup c.interval

@[simp]
theorem lo_le_hi : c.lo ≤ c.hi :=
  Real.sInf_le_sSup _
    (IsCompact.bddBelow c.isCompact_interval)
    (IsCompact.bddAbove c.isCompact_interval)

@[simp]
theorem icc_lo_hi_eq_interval : Set.Icc c.lo c.hi = c.interval :=
  (eq_Icc_of_connected_compact c.isConnected_interval c.isCompact_interval).symm

theorem mem_interval_iff {x : ℝ} : x ∈ c.interval ↔ c.lo ≤ x ∧ x ≤ c.hi := by
  simp only [← icc_lo_hi_eq_interval, Set.mem_Icc]

protected noncomputable def loEndpoint (c : Path' X) : X :=
  c.func c.lo

protected noncomputable def hiEndpoint (c : Path' X) : X :=
  c.func c.hi

protected def mk'
    (f : ℝ → X) (a b : ℝ) (h₁ : a ≤ b) (h₂ : ContinuousOn f (Set.Icc a b)) : Path' X :=
  ⟨f, Set.Icc a b, isCompact_Icc, isConnected_Icc h₁, Set.nonempty_Icc.mpr h₁, h₂⟩

@[ext]
theorem ext : ∀ {c₁ c₂ : Path' X}, c₁.func = c₂.func → c₁.interval = c₂.interval → c₁ = c₂
| ⟨⟨_, _, _, _, _⟩, _⟩, ⟨⟨_, _, _, _, _⟩, _⟩, h₁, h₂ => by simp_all only

def const (x : X) : Path' X :=
  Path'.mk' (fun _ ↦ x) 0 1 (by linarith) continuousOn_const

-- TODO: Should `IsClosed` be defined as a typeclass?
def IsClosed (c : Path' X) : Prop :=
  c.loEndpoint = c.hiEndpoint

def IsSimple (c : Path' X) : Prop :=
  Set.InjOn c.func c.interval

def IsArc (c : Path' X) : Prop :=
  c.loEndpoint ≠ c.hiEndpoint

def IsSimpleClosed (c : Path' X) : Prop :=
  c.IsClosed ∧ Set.InjOn c.func (c.interval \ {c.hi})

def IsSimpleArc (c : Path' X) : Prop :=
  c.IsArc ∧ c.IsSimple

theorem isSimpleClosed_isClosed (h : c.IsSimpleClosed) : c.IsClosed :=
  h.1

theorem isSimpleArc_isArc (h : c.IsSimpleArc) : c.IsArc :=
  h.1

theorem isSimpleArc_isSimple (h : c.IsSimpleArc) : c.IsSimple :=
  h.2

noncomputable def IsClosed.shift
    (c : Path' X) (h₁ : c.IsClosed) (new_lo : ℝ) (h₂ : c.lo ≤ new_lo) (h₃ : new_lo ≤ c.hi) :=
  Path'.mk' (fun x ↦
      if x < new_lo then c.func (x - new_lo + c.lo) else
      if new_lo + c.hi - c.lo < x then c.func (x - new_lo + c.lo) else
      if x ≤ c.hi then c.func x else c.func (x - c.hi + c.lo))
    new_lo (c.hi - c.lo + new_lo)
    ((le_add_iff_nonneg_left _).mpr (sub_nonneg.mpr lo_le_hi))
    sorry

def IsClosed.ProperlyEquivalent
    (c₁ : Path' X) (c₂ : Path' X) (h : c₂.IsClosed) : Prop :=
  ∃ (e : ℝ) (f : ℝ → ℝ) (he₁ : c₂.lo ≤ e) (he₂ : e ≤ c₂.hi),
    let c := IsClosed.shift c₂ h e he₁ he₂
    ContinuousOn f c.interval ∧ StrictMonoOn f c.interval ∧
    f c.lo = c₁.lo ∧ f c.hi = c₁.hi ∧
    ∀ x ∈ c.interval, c.func x = c₁.func (f x)

set_option linter.unusedVariables false in
def IsArc.ProperlyEquivalent
    (c₁ : Path' X) (c₂ : Path' X) (h : c₂.IsArc) : Prop :=
  ∃ f : ℝ → ℝ,
    ContinuousOn f c₂.interval ∧ StrictMonoOn f c₂.interval ∧
    f c₂.lo = c₁.lo ∧ f c₂.hi = c₂.hi ∧
    ∀ x ∈ c₂.interval, c₂.func x = c₁.func (f x)

def ProperlyEquivalent (c₁ c₂ : Path' X) : Prop :=
  (∃ (h : c₂.IsClosed), IsClosed.ProperlyEquivalent c₁ _ h) ∨
  (∃ (h : c₂.IsArc), IsArc.ProperlyEquivalent c₁ _ h)

theorem ProperlyEquivalent.rfl (c : Path' X) : c.ProperlyEquivalent c :=
  sorry

theorem ProperlyEquivalent.symm (h : c₁.ProperlyEquivalent c₂) : c₂.ProperlyEquivalent c₁ :=
  sorry

theorem ProperlyEquivalent.trans
    (h₁ : c₁.ProperlyEquivalent c₂) (h₂ : c₂.ProperlyEquivalent c₃) :
    c₁.ProperlyEquivalent c₃ :=
  sorry

theorem ProperlyEquivalent.eqv : Equivalence (@ProperlyEquivalent X _) :=
  ⟨ProperlyEquivalent.rfl, ProperlyEquivalent.symm, ProperlyEquivalent.trans⟩

instance isSetoid : Setoid (Path' X) :=
  ⟨ProperlyEquivalent, ProperlyEquivalent.eqv⟩

-- TODO: Should `IsConst` be defined as a typeclass?
def IsConst (c : Path' X) : Prop :=
  ∃ x, c ≈ const x

section IsConst

@[simp]
theorem const_isConst {x : X} : IsConst (const x) :=
  ⟨x, ProperlyEquivalent.rfl _⟩

end IsConst

protected def image (c : Curve' X) : Set X :=
  c.func '' c.interval

section Image

theorem image_eq_of_eqv (h : c₁.ProperlyEquivalent c₂) : c₁.image = c₂.image :=
  sorry

end Image

noncomputable def inverse (c : Path' X) : Path' X :=
  Path'.mk' (fun x ↦ c.func (c.lo + c.hi - x)) c.lo c.hi lo_le_hi
   sorry

noncomputable instance : Inv (Path' X) :=
  ⟨inverse⟩

section Inverse

@[simp]
theorem inverse_idemp : (c⁻¹)⁻¹ = c :=
  sorry

theorem inverse_inj (h : c₁⁻¹ = c₂⁻¹) : c₁ = c₂ := by
  rw [← @inverse_idemp _ _ c₁, h, inverse_idemp]

@[simp]
theorem inverse_inj_iff : c₁⁻¹ = c₂⁻¹ ↔ c₁ = c₂ :=
  ⟨inverse_inj, fun h ↦ h ▸ rfl⟩

end Inverse

noncomputable def composition
    (c₁ c₂ : Path' X) (h₁ : c₁.hi = c₂.lo) (h₂ : c₁.hiEndpoint = c₂.loEndpoint) : Path' X :=
  Path'.mk' (fun x ↦ if x < c₁.hi then c₁.func x else c₂.func x)
    c₁.lo c₂.hi (le_trans lo_le_hi (h₁ ▸ lo_le_hi))
    sorry

section Composition

variable {c₃ : Path' X}

@[simp]
theorem composition_lo
    (h₁ : c₁.hi = c₂.lo) (h₂ : c₁.hiEndpoint = c₂.loEndpoint) :
    (composition c₁ c₂ h₁ h₂).lo = c₁.lo :=
  sorry

@[simp]
theorem composition_hi
    (h₁ : c₁.hi = c₂.lo) (h₂ : c₁.hiEndpoint = c₂.loEndpoint) :
    (composition c₁ c₂ h₁ h₂).hi = c₂.hi := by
  sorry

-- TODO: Check if `rw` works well.
theorem composition_trans
    (h₁ : c₁.hi = c₂.lo) (h₂ : c₁.func c₁.hi = c₂.func c₂.lo)
    (h₃ : c₂.hi = c₃.lo) (h₄ : c₂.func c₂.hi = c₃.func c₃.lo) :
    composition (composition c₁ c₂ h₁ h₂) c₃ (composition_hi h₁ h₂ ▸ h₃) sorry =
    composition c₁ (composition c₂ c₃ h₃ h₄) (composition_lo h₃ h₄ ▸ h₁) sorry := by
  sorry

@[simp]
theorem composition_loEndpoint
    (h₁ : c₁.hi = c₂.lo) (h₂ : c₁.hiEndpoint = c₂.loEndpoint) :
    (composition c₁ c₂ h₁ h₂).loEndpoint = c₁.loEndpoint :=
  sorry

@[simp]
theorem composition_hiEndpoint
    (h₁ : c₁.hi = c₂.lo) (h₂ : c₁.hiEndpoint = c₂.loEndpoint) :
    (composition c₁ c₂ h₁ h₂).hiEndpoint = c₂.hiEndpoint :=
  sorry

end Composition

end Path'

def Path (X : Type*) [TopologicalSpace X] :=
  Quotient (@Curve'.isSetoid X _)

namespace Curve

variable {X : Type*} [TopologicalSpace X]
variable {c c₁ c₂ c₃ : Curve X}

def ofCurve' :=
  Quot.mk (@Curve'.isSetoid X _)

instance : Coe (Curve' X) (Curve X) :=
  ⟨ofCurve'⟩

@[simp]
theorem quot_mk_to_coe (c : Curve' X) : @Eq (Curve X) ⟦c⟧ c :=
  rfl

@[simp]
theorem quot_mk_to_coe' (c : Curve' X) : @Eq (Curve X) (Quot.mk (· ≈ ·) c) c :=
  rfl

@[simp]
theorem quot_mk_to_coe'' (c : Curve' X) : @Eq (Curve X) (Quot.mk Setoid.r c) c :=
  rfl

@[simp]
theorem lift_coe
    {α : Type*} (c : Curve' X) (f : Curve' X → α) (h : ∀ a b : Curve' X, a ≈ b → f a = f b) :
    Quotient.lift f h (c : Curve X) = f c :=
  rfl

def lo_endpoint (c : Curve X) : X :=
  sorry

def const (x : X) : Curve X :=
  Curve'.const x

def image (c : Curve X) : Set X :=
  Quotient.lift Curve'.image (@Curve'.image_eq_of_eqv _ _) c

def composition (c₁ c₂ : Curve) (h : 

end Curve

