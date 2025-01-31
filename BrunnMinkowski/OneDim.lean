import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.MeasureTheory.Group.Pointwise
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
-- #min_imports

-- LeanSearch
import LeanSearchClient
-- #leansearch "Union of two compact sets is also compact?"

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

-- translation invariance of measure --

open Set Pointwise Filter MeasureTheory MeasureTheory.Measure TopologicalSpace

theorem measure_translation_of_set (s : Set ℝ) (c : ℝ) : volume (image (fun x ↦ x + c) s) = volume s := by
  simp only [image_add_right, measure_preimage_add_right]

#check measure_translation_of_set
#check measure_union_add_inter
#check MeasureTheory.measure_mono
#check IsCompact.sSup_mem
#check IsCompact.sInf_mem
#check singleton_subset_iff
#check add_subset_add_right

#check MeasurableSet.const_vadd

#check Real.volume_singleton

-- It's a shame
example (A B : Set ℝ) : A + B = B + A := by
  exact Set.addCommMonoid.proof_1 A B

lemma volume_le_volume_add_right
    {A B : Set ℝ} (hB : B.Nonempty)
    : volume A ≤ volume (A + B) := by
  obtain ⟨b, hb⟩ := hB -- hB is a pair of b and proof of b in B
  calc
    volume A = volume (A + {b}) := by
      rw [add_singleton, image_add_right,
      measure_preimage_add_right]
    _ ≤ volume (A + B) := by
      apply measure_mono
      apply add_subset_add_left
      rw [singleton_subset_iff]
      exact hb

lemma volume_le_volume_add_left
    {A B : Set ℝ} (hB : B.Nonempty)
    : volume A ≤ volume (B + A) := by
  rw [addCommMonoid.proof_1 B]
  exact volume_le_volume_add_right hB

-- Maybe (or maybe not) factor out the lemmas below
/-
have hhh : volume A ≤ volume C := by
  calc
    volume A ≤ volume (A + B) := volume_le_volume_add_right hB
    _ ≤ volume C := by
      apply measure_mono
      exact h
have hhh' : volume B ≤ volume C := by
  calc
    volume B ≤ volume (A + B) := volume_le_volume_add_left hA
    _ ≤ volume C := by
      apply measure_mono
      exact h
-/

#check MeasurableSet.exists_isCompact_diff_lt

#check MeasurableSet.exists_isCompact_lt_add

-- important TODO: complete this
lemma MeasurableSet.exists_isCompact_Nonempty_diff_lt
    {α : Type} [MeasurableSpace α] {μ : Measure α} [TopologicalSpace α]
    [OpensMeasurableSpace α] [T2Space α] [μ.InnerRegularCompactLTTop]
    {A : Set α} (hA : A.Nonempty) (mA : MeasurableSet A) (h'A : μ A ≠ ⊤)
    {ε : ENNReal} (hε : ε ≠ 0) : ∃ K ⊆ A, K.Nonempty ∧ IsCompact K ∧ μ (A \ K) < ε := by
  -- rcases mA.exists_isCompact_diff_lt h'A hε with ⟨K, inclusion_K, cpt_K, diff_K⟩
  obtain ⟨K, inclusion_K, cpt_K, diff_K⟩ := mA.exists_isCompact_diff_lt h'A hε
  by_cases nonempty_K : K.Nonempty
  · exact ⟨K, inclusion_K, nonempty_K, cpt_K, diff_K⟩
  -- push_neg at nonempty_K
  obtain ⟨a, ha⟩ := hA
  use {a}
  simp [singleton_nonempty, isCompact_singleton]
  constructor
  · exact ha
  · push_neg at nonempty_K
    have small_A : μ A < ε := by
      rw [nonempty_K] at diff_K
      simp_all
    have bound_mAa : μ (A \ {a}) ≤ μ A := by simp only [diff_subset, measure_mono]
      -- have feather : A \ {a} ⊆ A := by exact diff_subset
      -- exact measure_mono feather
    calc μ (A \ {a}) ≤ μ A := by exact bound_mAa
    _ < ε := by exact small_A

lemma one_dim_BMInequality (A B C : Set ℝ)
    -- TODO: remove the line below
    -- [TopologicalSpace ℝ] [OpensMeasurableSpace ℝ] [T2Space ℝ]
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty)
    (mA : MeasurableSet A) (mB : MeasurableSet B) (mC : MeasurableSet C)
    (h : A + B ⊆ C)
    : volume A + volume B ≤ volume C := by
    --
  by_cases finA : volume A = ⊤
  · -- A is infinite
    rw [finA, _root_.top_add, ← finA]
    apply le_trans
      (volume_le_volume_add_right hB)
      (measure_mono h)
  -- Now assume A is finite
  by_cases finB : volume B = ⊤
  · -- B is infinite
    rw [finB, _root_.add_top, ← finB]
    apply le_trans
      (volume_le_volume_add_left hA)
      (measure_mono h)
  -- Now assume B is finite
  wlog cAB : IsCompact A ∧ IsCompact B with goal_cpt
  · -- Prove non-cpt A, B case assuming cpt A, B case
    apply le_of_forall_pos_lt_add'
    -- le_of_forall_pos_le_add
    intros ε hε
    have hε' : (ε/2) ≠ 0 := by
      by_contra he
      have he : ε = 0 := by
        rw [ENNReal.div_eq_zero_iff] at he
        simp_all only [and_imp, not_and, ENNReal.ofNat_ne_top, or_false]
      rw [he] at hε
      rw [lt_self_iff_false] at hε
      exact hε
    obtain ⟨Aε, inclusion_cptA, nonempty_cptA, h_cptA, diff_cptA⟩ :=
      MeasurableSet.exists_isCompact_Nonempty_diff_lt hA mA finA hε'
    obtain ⟨Bε, inclusion_cptB, nonempty_cptB, h_cptB, diff_cptB⟩ :=
      MeasurableSet.exists_isCompact_Nonempty_diff_lt hB mB finB hε'

    -- TO-check: To measure the volume of Aε or Bε, measurability is needed?
    have mAε : MeasurableSet Aε := by exact IsCompact.measurableSet h_cptA
    have mBε : MeasurableSet Bε := by exact IsCompact.measurableSet h_cptB
    -------------------------------------------------

    have finAε : volume Aε ≠ ⊤ := by
      by_contra inftyAε
      have feather : volume Aε ≤ volume A := by exact measure_mono inclusion_cptA
      simp_all

    have finBε : volume Bε ≠ ⊤ := by
      by_contra inftyBε
      have feather : volume Bε ≤ volume B := by exact measure_mono inclusion_cptB
      simp_all

    have wma_cpt : volume Aε + volume Bε ≤ volume C := by
      have inclusion_cpt : Aε + Bε ⊆ C := by
        have feather : Aε + Bε ⊆ A + B := by
          intros x hx
          have hx' : ∃ a ∈ Aε, ∃ b ∈ Bε, a + b = x := by exact mem_add.mpr hx
          obtain ⟨a, ha, b, hb, hx'⟩ := hx'
          have ha : a ∈ A := by exact inclusion_cptA ha
          have hb : b ∈ B := by exact inclusion_cptB hb
          have h : a + b ∈ A + B := by apply add_mem_add ha hb
          rw [← hx']
          exact h
        calc Aε + Bε ⊆ A + B := by apply feather
        _ ⊆ C := by apply h
      have feather : IsCompact Aε ∧ IsCompact Bε := by apply And.intro h_cptA h_cptB
      exact goal_cpt Aε Bε C nonempty_cptA nonempty_cptB hC mAε mBε mC inclusion_cpt finAε finBε feather

    have diff_cptA' : volume A < volume Aε + ε/2 := by
      have feather1 : volume A = volume Aε + volume (A\Aε) := by
        have feather2 : volume (A ∩ Aε) + volume (A \ Aε) = volume A := by apply measure_inter_add_diff A mAε
        have feather3 : volume (A ∩ Aε) = volume Aε := by rw [inter_eq_right.mpr inclusion_cptA]
        calc volume A = volume (A ∩ Aε) + volume (A \ Aε) := by rw [←feather2]
        _ = volume Aε + volume (A \ Aε) := by rw [feather3]
      calc volume A = volume Aε + volume (A \ Aε) := by apply feather1
      _ < volume Aε + ε/2 := by exact ENNReal.add_lt_add_left finAε diff_cptA

    have diff_cptB' : volume B < volume Bε + ε/2 := by
      have feather1 : volume B = volume Bε + volume (B\Bε) := by
        have feather2 : volume (B ∩ Bε) + volume (B \ Bε) = volume B := by apply measure_inter_add_diff B mBε
        have feather3 : volume (B ∩ Bε) = volume Bε := by rw [inter_eq_right.mpr inclusion_cptB]
        calc volume B = volume (B ∩ Bε) + volume (B \ Bε) := by rw [←feather2]
        _ = volume Bε + volume (B \ Bε) := by rw [feather3]
      calc volume B = volume Bε + volume (B \ Bε) := by apply feather1
      _ < volume Bε + ε/2 := by exact ENNReal.add_lt_add_left finBε diff_cptB

    calc volume A + volume B < volume Aε + ε/2 + (volume Bε + ε/2) := by
            exact ENNReal.add_lt_add diff_cptA' diff_cptB'
    _ = volume Aε + volume Bε + ε := by
      -- ring_nf
      simp only [add_left_comm, add_halves, ←add_assoc]
      rw [add_assoc]
      simp_all [add_assoc]
    _ ≤  volume C + ε := by exact add_le_add_right wma_cpt ε

  -- Prove the theorem assuming cpt A, B
  obtain ⟨cA, cB⟩ := cAB
  set At := sInf B +ᵥ A with eq_At
  set Bt := sSup A +ᵥ B with eq_Bt
  have eq_At_vol : volume At = volume A := by
    rw [eq_At]
    simp only [measure_vadd]
  have eq_Bt_vol : volume Bt = volume B := by
    rw [eq_Bt]
    simp only [measure_vadd]
  have sub_At : At ⊆ C := by
    rw [eq_At]
    apply Subset.trans _ h
    rw [add_comm]
    rw [← Set.singleton_vadd]
    apply Set.add_subset_add_right
    simp only [singleton_subset_iff]
    exact cB.sInf_mem hB
  have sub_Bt : Bt ⊆ C := by
    rw [eq_Bt]
    apply Subset.trans _ h
    rw [← Set.singleton_vadd]
    apply Set.add_subset_add_right
    simp only [singleton_subset_iff]
    exact cA.sSup_mem hA
  have cup_At_Bt : At ∪ Bt ⊆ C := by
    simp only [union_subset_iff]
    constructor
    · exact sub_At
    · exact sub_Bt
  have m_zero_AtBt : volume (At ∩ Bt) = 0 := by
    have cap_At_Bt : At ∩ Bt = {sSup A + sInf B} := by
      rw [Set.ext_iff]
      intro x
      constructor
      · intro hx
        simp_all
        obtain ⟨xAt, xBt⟩ := hx
        apply mem_vadd_set.mp at xAt
        cases' xAt with a ha
        obtain ⟨ha, hax⟩ := ha
        apply mem_vadd_set.mp at xBt
        cases' xBt with b hb
        obtain ⟨hb, hbx⟩ := hb
        have upper_x : x ≤ sInf B + sSup A := by
          rw [← hax]
          have a_le_supA : a ≤ sSup A := by
            have bdd_A : BddAbove A := by exact IsCompact.bddAbove cA
            exact le_csSup bdd_A ha
          simp [a_le_supA]
        have lower_x : sSup A + sInf B ≤ x := by
          rw [← hbx]
          have infB_le_b : sInf B ≤ b := by
            have bdd_B : BddBelow B := by exact IsCompact.bddBelow cB
            exact csInf_le bdd_B hb
          simp [infB_le_b]
        rw [add_comm] at upper_x
        exact le_antisymm upper_x lower_x
      · intro hx
        simp at hx
        constructor
        · have x_At : sSup A + sInf B ∈ sInf B +ᵥ A := by
            have supA_A : sSup A ∈ A := by exact IsCompact.sSup_mem cA hA
            rw [add_comm]
            apply vadd_mem_vadd_set_iff.mpr
            exact supA_A
          simp only [hx, eq_At, x_At]
        · have x_Bt : sSup A  + sInf B ∈ sSup A +ᵥ B := by
            have infB_B : sInf B ∈ B := by exact IsCompact.sInf_mem cB hB
            apply vadd_mem_vadd_set_iff.mpr
            exact infB_B
          simp only [hx, eq_Bt, x_Bt]
    calc volume (At ∩ Bt) = volume {sSup A + sInf B} := by rw [cap_At_Bt]
    _ = 0 := by rw [Real.volume_singleton]
  calc volume A + volume B = volume At + volume Bt - 0 := by simp [eq_At_vol, eq_Bt_vol]
  _ = volume At + volume Bt - volume (At ∩ Bt) := by rw [← m_zero_AtBt]
  _ = volume (At ∪ Bt) := by
    have vol_union_AtBt : volume (At ∪ Bt) + volume (At ∩ Bt) = volume At + volume Bt := by
      have mBt : MeasurableSet Bt := by exact MeasurableSet.const_vadd mB (sSup A)
      exact measure_union_add_inter At mBt
    simp_all
  _ ≤ volume C := by exact measure_mono cup_At_Bt
