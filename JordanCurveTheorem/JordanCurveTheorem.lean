import Mathlib

-- Theorem 8.31: IsOpen.isConnected_iff_isPathConnected

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

section

variable {p : ENNReal} {α : ι → Type*} [Fact (1 ≤ p)]

--open Set EMetric in
--instance : TopologicalSpace (PiLp p α) where
--  IsOpen s :=
--    ∃ S : Set (Set (PiLp p α)), (∀ t ∈ S, ∃ (x : PiLp p α) (ε : ENNReal), t = ball x ε) ∧ s = ⋃₀ S
--  isOpen_univ := ⟨{s : Set (PiLp p α) | ∃ x, s = ball x 1}, by
--    simp only [mem_setOf_eq, forall_exists_index, forall_eq_apply_imp_iff, exists_apply_eq_apply2',
--      implies_true, true_and]
--    ext x; simp_rw [mem_sUnion, mem_setOf_eq]
--    exact
--      ⟨fun _ ↦ ⟨ball x 1, ⟨⟨x, rfl⟩, mem_ball.mpr (edist_self x ▸ zero_lt_one)⟩⟩,
--        fun _ ↦ mem_univ _⟩⟩

end

variable {x y : ℝ²}

/-- A Jordan curve is an injective path. -/
structure JordanCurve (x y : ℝ²) extends Path x y where
  injective_toFun : Function.Injective toFun

def jordanCurve_separated_components (c : JordanCurve x x) :=
  TopologicalSpace.induced (fun x : {a : ℝ² // ∀ x, a ≠ c.toFun x} ↦ x.val)
    (TopologicalSpace.generateFrom (x ∈ ·))

theorem jordan_curve_theorem
    {c : JordanCurve x x} :
    (@Set.univ (ConnectedComponents {a : ℝ² // ∀ x, a ≠ c.toPath x})).ncard = 2 := by
  sorry

