import Mathlib

theorem Path.isClosed
    {X : Type*} [TopologicalSpace X] {x y : X} {p : Path x y} :
    IsClosed (p '' univ) :=
  sorry

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- A Jordan arc is an injective path. -/
structure JordanArc (s t : ℝ²) extends Path s t where
  injective_toFun : Function.Injective toFun

namespace JordanArc

open Set Metric Bornology

variable {s t : ℝ²}
variable {a : JordanArc s t}

instance : FunLike (JordanArc s t) unitInterval ℝ² where
  coe a := a.toFun
  coe_injective' := sorry

/-- An image of a Jordan curve `c` is a mapping of `c` from the unit circle to `ℝ²` -/
def image (a : JordanArc s t) : Set ℝ² :=
  a '' univ

theorem jordanPath_source_not_target (a : JordanArc s t) : s ≠ t := by
  intro h; simp_rw [← a.source', ← a.target'] at h; exact zero_ne_one (a.injective_toFun h)

end JordanArc

/-- A Jordan curve is an continuous injective map from $S^1$. -/
structure JordanCurve (p : ℝ²) extends Path p p where
  almost_injective_toFun : ∀ {x y}, toFun x = toFun y → x = y ∨ (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0)

namespace JordanCurve

open Set Metric Bornology

variable {p : ℝ²}
variable {c : JordanCurve p}

noncomputable instance : FunLike (JordanCurve p) Circle ℝ² where
  coe a x := a.toFun ⟨(x.argEquiv + Real.pi) / (2 * Real.pi), sorry⟩
  coe_injective' := sorry

def image (c : JordanCurve p) : Set ℝ² :=
  c '' univ

@[simp]
theorem mem_image_iff {q : ℝ²} : q ∈ c.image ↔ ∃ x : Circle, q = c x := by
  simp only [image, image_univ, mem_range]; tauto

theorem isBounded_image (c : JordanCurve p) : IsBounded c.image := by
  simp only [image_univ, isBounded_iff, mem_range, forall_exists_index, forall_apply_eq_imp_iff]
  use sSup {d : ℝ | ∃ x y : Circle, d = dist (c x) (c y)}
  intro _ h₁ _ h₂; rcases mem_image_iff.mp h₁ with ⟨x, h₁⟩; rcases mem_image_iff.mp h₂ with ⟨y, h₂⟩
  rw [h₁, h₂]; refine le_csSup ?_ (by tauto)
  sorry

def in_same_connected_component (T:Type) [TopologicalSpace T] (a b:T) := a ∈ connectedComponent b

lemma Jainszewski_weak (a b: ℝ²) (S T: Set ℝ²) (cs: IsCompact S) (ct: IsCompact T) (ccs: a ∈ connectedComponentIn (Sᶜ) b) (cct:a ∈ connectedComponentIn Tᶜ b): a ∈ connectedComponentIn (S ∪ T)ᶜ b := sorry

lemma Jainszewski (a b: ℝ²) (S T: Set ℝ²) (cs: IsCompact S) (ct: IsClosed T) (ccn: IsConnected (S ∩ T)) (ccs: a ∈ connectedComponentIn (Sᶜ) b) (cct:a ∈ connectedComponentIn Tᶜ b): a ∈ connectedComponentIn (S ∪ T)ᶜ b := sorry

lemma exists_double_arc (a:ℝ²) (g: JordanCurve a): exists (b:ℝ²) (u:JordanArc a b) (d:JordanArc b a), u.image ∩ d.image = {a,b} ∧ u.image ∪ d.image = g.image :=sorry

theorem Jordan_curve (a:ℝ²) (c:JordanCurve a): exists (inner outer: Set ℝ²), (inner.Nonempty) ∧ (outer.Nonempty) ∧ (IsOpen inner) ∧ (IsOpen outer) ∧ (IsConnected inner) ∧ (IsConnected outer) ∧ (IsBounded inner) ∧ (¬ IsBounded outer) ∧ (inner ∩ outer =∅ ) ∧ (inner ∪ outer = c.imageᶜ ):=by sorry
/-
-- TODO: Remove `noncomputable` if possible.
/-- `outerComponent` is the outer component. -/
noncomputable def outerComponent (c : JordanCurve p) : Set ℝ² :=
  let r : ℝ := sSup ((fun x ↦ dist 0 (c x)) '' univ)
  connectedComponentIn {q : ℝ² | ∀ x, q ≠ c.toFun x} !₂[r + 1, 0]

-- TODO: Remove `noncomputable` if possible.
/-- `innerComponent` is the inner component. -/
noncomputable def innerComponent (c : JordanCurve p) : Set ℝ² :=
  {q : ℝ² | q ∉ outerComponent c ∧ ∀ x, q ≠ c x}

theorem disjoint_outerComponent_innerComponent : Disjoint c.outerComponent c.innerComponent :=
  sorry

theorem disjoint_image_outerComponent : Disjoint c.image c.outerComponent :=
  sorry

theorem disjoint_image_innerComponent : Disjoint c.image c.innerComponent :=
  sorry

theorem isCobounded_outerComponent : IsCobounded c.outerComponent :=
  sorry

theorem isOpen_outerComponent : IsOpen c.outerComponent :=
  sorry

theorem isConnected_outerComponent : IsConnected c.outerComponent :=
  isConnected_connectedComponentIn_iff.mpr (by
    simp only [ContinuousMap.toFun_eq_coe, Path.coe_toContinuousMap, ne_eq, Subtype.forall,
      mem_Icc, image_univ, mem_setOf_eq]
    rintro r ⟨h₁, h₂⟩ h₃
    sorry)

theorem isBounded_innerComponent : IsBounded c.innerComponent :=
  sorry

theorem isOpen_innerComponent : IsOpen c.innerComponent :=
  sorry

-- Jordan Curve theorem
theorem isConnected_innerComponent : IsConnected c.innerComponent :=
  sorry

-/
end JordanCurve
