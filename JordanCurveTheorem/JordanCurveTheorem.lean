import Mathlib

-- Theorem 8.31: IsOpen.isConnected_iff_isPathConnected

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- A Jordan arc is an injective path. -/
structure JordanArc (s t : ℝ²) extends Path s t where
  injective_toFun : Function.Injective toFun

namespace JordanArc

variable {s t : ℝ²}
variable {a : JordanArc s t}

instance : FunLike (JordanArc s t) unitInterval ℝ² where
  coe a := a.toFun
  coe_injective' := sorry

theorem jordanPath_source_ne_target (a : JordanArc s t) : s ≠ t := by
  intro h; simp_rw [← a.source', ← a.target'] at h; exact zero_ne_one (a.injective_toFun h)

end JordanArc

/-- A Jordan curve is an continuous injective map from $S^1$. -/
structure JordanCurve (p : ℝ²) extends Path p p where
  almost_injective_toFun : ∀ {x y}, toFun x = toFun y → x = y ∨ (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0)

namespace JordanCurve

variable {p : ℝ²}
variable {c : JordanCurve p}

instance : FunLike (JordanCurve p) Circle ℝ² where
  coe a x := sorry
  coe_injective' := sorry

open Set Metric

theorem jordanCurve_bounded :
    ∃ r, c.toFun '' univ ⊆ ball 0 r := by
  sorry

-- TODO: Remove `noncomputable` if possible.
/-- `outerComponent` is the outer component. -/
noncomputable def outerComponent (c : JordanCurve p) : Set ℝ² :=
  let r : ℝ := Classical.choose (@jordanCurve_bounded p c)
  connectedComponentIn {q : ℝ² | ∀ x, q ≠ c.toFun x} !₂[r, 0]

-- TODO: Remove `noncomputable` if possible.
/-- `innerComponent` is the inner component. -/
noncomputable def innerComponent (c : JordanCurve p) : Set ℝ² :=
  {q : ℝ² | q ∉ outerComponent c ∧ ∀ x, q ≠ c x}

theorem isOpen_outerComponent : IsOpen c.outerComponent :=
  sorry

theorem isConnected_outerComponent :
    IsConnected c.outerComponent :=
  isConnected_connectedComponentIn_iff.mpr (by
    simp only [ContinuousMap.toFun_eq_coe, Path.coe_toContinuousMap, ne_eq, Subtype.forall,
      mem_Icc, image_univ, mem_setOf_eq]
    rintro r ⟨h₁, h₂⟩ h₃

    sorry)

theorem isOpen_innerComponent : IsOpen c.innerComponent :=
  sorry

-- Jordan Curve theorem
theorem isConnected_innerComponent :
    IsConnected c.innerComponent :=
  sorry

end JordanCurve

-- TODO: Should we generalize this?
-- 1. Jordan–Brouwer separation theorem
-- 2. Jordan–Schoenflies theorem

