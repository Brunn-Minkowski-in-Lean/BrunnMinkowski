import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
-- #min_imports

-- LeanSearch
-- import LeanSearchClient

-- #leansearch "Union of two compact sets is also compact?"
--

-- InnerRegularity

-- InnerRegular mu : Prop
-- Need: InnerRegular volume

#check MeasurableSet.exists_isCompact_diff_lt
-- Want to apply the lemma above to [0, 1] in R
#check Set.Ioo 0 1
#check MeasurableSet.exists_isCompact_diff_lt (measurableSet_Ioo : MeasurableSet (Set.Ioo 0 1))

variable (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
#check MeasurableSet.exists_isCompact_diff_lt hA

-- μ(A \ Aε) = μ(A) - μ(Aε)

#check MeasureTheory.measure_diff

-- When α = ℝ,
-- (∀ (ε : α), 0 < ε → a < b + ε) → a ≤ b

#check le_of_forall_pos_lt_add

variable (a b : ℝ) (he : ∀ (ε : ℝ), 0 < ε → a < b + ε)
#check le_of_forall_pos_lt_add

--

-- translation invariance of measure --

open Set Pointwise Filter MeasureTheory MeasureTheory.Measure TopologicalSpace

theorem measure_translation_of_set (s : Set ℝ) (c : ℝ) : volume (image (fun x ↦ x + c) s) = volume s := by
  simp only [image_add_right, measure_preimage_add_right]

#check measure_translation_of_set

--

#check measure_union_add_inter

#check MeasureTheory.measure_mono


#check IsCompact.sSup_mem
#check IsCompact.sInf_mem

def even (n : ℕ) : Prop := by sorry
-- even 3 : Prop  (`even 3` is a proposition)
lemma four_is_even : even 4 := by sorry
-- four_is_even : even 4 (`four_is_even` is a proof of `even 4`)

-- Requrires an instance of type `MeasurableSpace α`
lemma some_lemma (α : Type) [inst_mea : MeasurableSpace α] [inst_TopSp : TopologicalSpace α] : ∀ x : α, 1 = 1 := by
  -- assumes Lean has an instance of [MeasurableSpace α]
  sorry


-- There is some [inst_mea : MeasurableSpace ℝ] floating around somewhere in mathlib
-- somewhere in Mathlib, someone defined:
/-
instance realMeasurableInst : MeasurableSpace ℝ := by
  sorry
-/
-- What happens next, is that now Lean kernel 'knows' instance [MeasurableSpace ℝ]
-- internally, so whenever [MeasurableSpace ℝ] is required, kernel fills that out with
-- `realMeasurableInst`.
#check some_lemma ℝ

-- That's why above works.

example (a : ENNReal) : ⊤ + a = ⊤ := by
  simp only [_root_.top_add]

-- variable [Nonempty B]
-- #check Classical.arbitrary B

-- #check Set.Nonempty
#check singleton_subset_iff
#check add_subset_add_right
-- #check rw [addCommMonoid.proof_1]

-- ?????????????????????????????
example (A B : Set ℝ) : A + B = B + A := by
  rw [addCommMonoid.proof_1 A]
-- ?????????????????????????????

lemma one_dim_BMInequality (A B C : Set ℝ)
    -- TODO: remove the line below
    -- [TopologicalSpace ℝ] [OpensMeasurableSpace ℝ] [T2Space ℝ]
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty)
    (mA : MeasurableSet A) (mB : MeasurableSet B) (mC : MeasurableSet C)
    (h : A + B ⊆ C)
    : volume A + volume B ≤ volume C := by
    --
  have hh : volume A ≤ volume (A + B) := by
    obtain ⟨b, hb⟩ := hB -- hB is a pair of b and proof of b in B
    have trans_inv : volume A = volume (A + {b}) := by simp
    have TaaDa : volume (A + {b}) ≤ volume (A + B) := by
      have singleton_inclusion : A + {b} ⊆ A + B := by
        have hhhh : {b} ⊆ B := by
          apply singleton_subset_iff.mpr
          exact hb
        exact add_subset_add_left hhhh
      apply measure_mono
      exact singleton_inclusion
    -- rw [trans_inv]
    -- apply measure_mono
    -- exact singleton_inclusion
    calc
      volume A = volume (A + {b}) := by apply trans_inv
      _ ≤ volume (A + B) := by exact TaaDa
  --
  have hh' : volume B ≤ volume (B + A) := by
    obtain ⟨a, ha⟩ := hA -- hB is a pair of b and proof of b in B
    have trans_inv : volume B = volume (B + {a}) := by simp
    have TaaDa : volume (B + {a}) ≤ volume (B + A) := by
      have singleton_inclusion : B + {a} ⊆ B + A := by
        have hhhh : {a} ⊆ A := by
          apply singleton_subset_iff.mpr
          exact ha
        exact add_subset_add_left hhhh
      apply measure_mono
      exact singleton_inclusion
    calc
      volume B = volume (B + {a}) := by apply trans_inv
      _ ≤ volume (B + A) := by exact TaaDa
  --
  have hhh : volume A ≤ volume C := by
    calc
      volume A ≤ volume (A + B) := by exact hh
      _ ≤ volume C := by
        apply measure_mono
        exact h
  --
  have hhh' : volume B ≤ volume C := by
    calc
      volume B ≤ volume (B + A) := by exact hh'
      _ = volume (A + B) := by rw [addCommMonoid.proof_1 A]
      _ ≤ volume C := by
        apply measure_mono
        exact h
  by_cases finA : volume A = ⊤
  · -- A is infinite
    rw [finA]
    simp
    rw [finA] at hhh
    simp at hhh
    exact hhh
  -- Now assume A is finite
  by_cases finB : volume B = ⊤
  · -- B is infinite
    rw [finB]
    simp
    rw [finB] at hhh'
    simp at hhh'
    exact hhh'
  -- Now assume B is finite
  wlog cAB : IsCompact A ∧ IsCompact B with goal_cpt
  · -- Prove non-cpt A, B case assuming cpt A, B case
    -- have yy : (1 / 10 : ENNReal) ≠ 0 := by sorry
    -- have tt := mA.exists_isCompact_diff_lt finA yy
    apply le_of_forall_pos_le_add
    intros ε hε
    have hε' : ε ≠ 0 := by sorry
    have cpt_A := by apply mA.exists_isCompact_diff_lt finA hε'
    have cpt_B := by apply mB.exists_isCompact_diff_lt finB hε'
    obtain ⟨Aε, inclusion_cptA, h_cptA, diff_cptA⟩ := cpt_A
    obtain ⟨Bε, inclusion_cptB, h_cptB, diff_cptB⟩ := cpt_B
    have inclusion_cpt : Aε + Bε ⊆ C := by
      have feather : Aε + Bε ⊆ A + B := by
        intros x hx
        have hx' : ∃ a ∈ Aε, ∃ b ∈ Bε, a + b = x := by
          exact mem_add.mpr hx
        obtain ⟨a, ha, b, hb, hx'⟩ := hx'
        have ha : a ∈ A := by aesop
        have hb : b ∈ B := by aesop
        have h : a + b ∈ A + B := by apply add_mem_add ha hb
        rw [← hx']
        exact h
      calc Aε + Bε ⊆ A + B := by apply feather
      _ ⊆ C := by apply h
    sorry

  -- Prove the theorem assuming cpt A, B
  obtain ⟨cA, cB⟩ := cAB
  set At := sInf B +ᵥ A with eq_At
  set Bt := sSup A +ᵥ B with eq_Bt
  have eq_At_vol : volume At = volume A := by
    rw [eq_At]
    simp?
  have eq_Bt_vol : volume Bt = volume B := by
    sorry
  have sub_At : At ⊆ C := by
    rw [eq_At]
    apply Subset.trans _ h
    rw [add_comm]
    rw [← Set.singleton_vadd]
    apply Set.add_subset_add_right
    simp?
    exact cB.sInf_mem hB
  have sub_Bt : Bt ⊆ C := by
    sorry
  have cup_At_Bt : At ∪ Bt ⊆ C := by
    sorry
  have cap_At_Bt : At ∩ Bt = {sSup A + sInf B} := by
    sorry
  sorry



theorem ineqPrekopaLeindler
  {t : ℝ} (h0t : 0 < t) (ht1 : t < 1) : 1 = 1 := by sorry
