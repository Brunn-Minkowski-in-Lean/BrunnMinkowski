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
import Mathlib.Algebra.Group.Pointwise.Set.Basic

variable (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)

open Set Pointwise Filter MeasureTheory MeasureTheory.Measure TopologicalSpace

lemma volume_le_volume_add_right
    {A B : Set ℝ} (hB : B.Nonempty)
    : volume A ≤ volume (A + B) := by
  obtain ⟨b, hb⟩ := hB
  calc
    volume A = volume (A + {b}) := by rw [add_singleton, image_add_right, measure_preimage_add_right]
    _ ≤ volume (A + B) := measure_mono (add_subset_add_left (singleton_subset_iff.mpr hb))

lemma volume_le_volume_add_left
    {A B : Set ℝ} (hB : B.Nonempty)
    : volume A ≤ volume (B + A) := by
  rw [addCommMonoid.proof_1 B]
  exact volume_le_volume_add_right hB

lemma measure_diff_singleton_lt {α : Type} [MeasurableSpace α] (μ : Measure α) (A : Set α) (a : α) : μ (A \ {a}) ≤ μ A := by simp only [diff_subset, measure_mono]

lemma ENNReal_div_two_ne_zero (ε : ENNReal) (hε : 0 < ε) : (ε/2) ≠ 0 := by
  by_contra he
  rw [ENNReal.div_eq_zero_iff] at he
  cases' he with zero_ε two_eq_top
  rw [zero_ε, lt_self_iff_false] at hε
  exact hε
  exact ENNReal.two_ne_top two_eq_top

lemma volume_ne_top_of_subset (finA : volume A ≠ ⊤) (h : Aε ⊆ A) : volume Aε ≠ ⊤ := by
  by_contra inftyAε
  have feather : volume Aε ≤ volume A := measure_mono h
  rw [inftyAε, top_le_iff] at feather
  exact finA feather

lemma volume_lt_subset_add_diff (mAε : MeasurableSet Aε) (finAε : volume Aε ≠ ⊤) (h : Aε ⊆ A) (diff : volume (A \ Aε) < ε / 2) : volume A < volume Aε + ε/2 := by
  have feather : volume A = volume Aε + volume (A \ Aε) := by rw [←measure_inter_add_diff A mAε, inter_eq_right.mpr h]
  rw [feather]
  exact ENNReal.add_lt_add_left finAε diff

lemma subset_add_subset_subset (h : A + B ⊆ C) (hInclA : Aε ⊆ A) (hInclB : Bε ⊆ B) : Aε + Bε ⊆ C := by
  intro x
  rintro ⟨a, haε, b, hbε, rfl⟩
  exact h (add_mem_add (hInclA haε) (hInclB hbε))

lemma add_with_halves_eq_one (a : ENNReal) (b : ENNReal) (ε : ENNReal) : a + ε/2 + (b + ε/2) = a + b + ε := by
  simp only [add_left_comm, add_halves, ←add_assoc]
  rw [add_assoc]
  simp_all [add_assoc]

lemma measure_translation_of_set (a : ℝ) : volume (a +ᵥ A) = volume A := by simp only [measure_vadd]

lemma sInf_of_cpt_vadd_subset (h: A + B ⊆ C) (hB : B.Nonempty) (cB : IsCompact B): sInf B +ᵥ A ⊆ C := by
  apply Subset.trans _ h
  rw [add_comm, ← Set.singleton_vadd]
  apply Set.add_subset_add_right
  simp only [singleton_subset_iff]
  exact cB.sInf_mem hB

lemma sSup_of_cpt_vadd_subset (h: A + B ⊆ C) (hA : A.Nonempty) (cA : IsCompact A): sSup A +ᵥ B ⊆ C := by
  apply Subset.trans _ h
  rw [← Set.singleton_vadd]
  apply Set.add_subset_add_right
  simp only [singleton_subset_iff]
  exact cA.sSup_mem hA

lemma a_le_supA (cA : IsCompact A) (ha : a ∈ A) : a ≤ sSup A := le_csSup (IsCompact.bddAbove cA) ha

lemma infA_le_a (cA : IsCompact A) (ha : a ∈ A) : sInf A ≤ a := csInf_le (IsCompact.bddBelow cA) ha

lemma volume_union_add_inter_eq_add (h : MeasurableSet B): volume (A ∪ B) + volume (A ∩ B) = volume A + volume B := measure_union_add_inter A h

lemma inter_sInf_sSup_eq_singleton (hA : A.Nonempty) (hB : B.Nonempty) (cA : IsCompact A) (cB : IsCompact B)
  (hAt : At = sInf B +ᵥ A) (hBt : Bt = sSup A +ᵥ B) : At ∩ Bt = {sSup A + sInf B} := by
  rw [Set.ext_iff]
  intro x
  constructor
  · rintro ⟨hxAt, hxBt⟩
    rw [hAt, mem_vadd_set] at hxAt
    rw [hBt, mem_vadd_set] at hxBt
    rcases hxAt with ⟨a, ha, hax⟩
    rcases hxBt with ⟨b, hb, hbx⟩
    have upper_x : x ≤ sInf B + sSup A := by simp [← hax, a_le_supA A cA ha]
    have lower_x : sSup A + sInf B ≤ x := by simp [← hbx, vadd_eq_add, add_le_add_iff_left, infA_le_a B cB hb]
    rw [add_comm] at upper_x
    exact le_antisymm upper_x lower_x
  · intro hx
    apply mem_singleton_iff.mp at hx
    constructor
    · have x_At : sSup A + sInf B ∈ sInf B +ᵥ A := by
        rw [add_comm]
        exact vadd_mem_vadd_set_iff.mpr (IsCompact.sSup_mem cA hA)
      simp only [hx, hAt, x_At]
    · have x_Bt : sSup A  + sInf B ∈ sSup A +ᵥ B := vadd_mem_vadd_set_iff.mpr (IsCompact.sInf_mem cB hB)
      simp only [hx, hBt, x_Bt]

lemma MeasurableSet.exists_isCompact_Nonempty_diff_lt
    {α : Type} [MeasurableSpace α] {μ : Measure α} [TopologicalSpace α]
    [OpensMeasurableSpace α] [T2Space α] [μ.InnerRegularCompactLTTop]
    {A : Set α} (hA : A.Nonempty) (mA : MeasurableSet A) (h'A : μ A ≠ ⊤)
    {ε : ENNReal} (hε : ε ≠ 0) : ∃ K ⊆ A, K.Nonempty ∧ IsCompact K ∧ μ (A \ K) < ε := by
  obtain ⟨K_tilde, inclusion_K_tilde, cpt_K_tilde, diff_K_tilde⟩ := mA.exists_isCompact_diff_lt h'A hε
  by_cases nonempty_K_tilde : K_tilde.Nonempty
  · exact ⟨K_tilde, inclusion_K_tilde, nonempty_K_tilde, cpt_K_tilde, diff_K_tilde⟩
  · obtain ⟨a, ha⟩ := hA
    refine ⟨{a}, singleton_subset_iff.mpr ha, singleton_nonempty a, isCompact_singleton, ?_⟩
    have small_A : μ A < ε := by
      push_neg at nonempty_K_tilde
      rw [nonempty_K_tilde, diff_empty] at diff_K_tilde
      exact diff_K_tilde
    calc μ (A \ {a}) ≤ μ A := measure_diff_singleton_lt μ A a
        _ < ε := small_A

lemma one_dim_BMInequality_infty (A B C : Set ℝ)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (h : A + B ⊆ C) (hInfty: volume A = ⊤ ∨ volume B = ⊤)
    : volume A + volume B ≤ volume C := by
      cases' hInfty with hInfty_A hInfty_B
      rw [hInfty_A, _root_.top_add, ← hInfty_A]
      exact le_trans (volume_le_volume_add_right hB) (measure_mono h)
      rw [hInfty_B, _root_.add_top, ← hInfty_B]
      exact le_trans (volume_le_volume_add_left hA) (measure_mono h)

lemma one_dim_BMInequality_cpt (A B C : Set ℝ)
    (hA : A.Nonempty) (hB : B.Nonempty) (mB : MeasurableSet B)
    (h : A + B ⊆ C)
    (cA : IsCompact A) (cB : IsCompact B)
    : volume A + volume B ≤ volume C := by

  set At := sInf B +ᵥ A with eq_At
  set Bt := sSup A +ᵥ B with eq_Bt

  have eq_At_vol : volume At = volume A := measure_translation_of_set A (sInf B)
  have eq_Bt_vol : volume Bt = volume B := measure_translation_of_set B (sSup A)

  have cup_At_Bt : At ∪ Bt ⊆ C := union_subset_iff.mpr ⟨(sInf_of_cpt_vadd_subset A B h hB cB), (sSup_of_cpt_vadd_subset A B h hA cA)⟩

  have m_zero_AtBt : volume (At ∩ Bt) = 0 := by
    have cap_At_Bt : At ∩ Bt = {sSup A + sInf B} := inter_sInf_sSup_eq_singleton A B hA hB cA cB eq_At eq_Bt
    rw [cap_At_Bt, Real.volume_singleton]

  calc volume A + volume B
  _ = volume At + volume Bt - 0 := by rw [eq_At_vol, eq_Bt_vol, tsub_zero]
  _ = volume At + volume Bt - volume (At ∩ Bt) := by rw [← m_zero_AtBt]
  _ = volume (At ∪ Bt) := by
    have vol_union_AtBt : volume (At ∪ Bt) + volume (At ∩ Bt) = volume At + volume Bt := volume_union_add_inter_eq_add At Bt (MeasurableSet.const_vadd mB (sSup A))
    have m_not_top_AtBt : volume (At ∩ Bt) ≠ ⊤ := by rw [m_zero_AtBt]; simp [ENNReal.zero_ne_top.symm]
    simp [←vol_union_AtBt, add_comm, ENNReal.add_sub_cancel_left, m_not_top_AtBt]
  _ ≤ volume C := measure_mono cup_At_Bt

lemma one_dim_BMInequality (A B C : Set ℝ)
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty)
    (mA : MeasurableSet A) (mB : MeasurableSet B) (mC : MeasurableSet C)
    (h : A + B ⊆ C)
    : volume A + volume B ≤ volume C := by
  by_cases hInfty : volume A = ⊤ ∨ volume B = ⊤
  · exact one_dim_BMInequality_infty A B C hA hB h hInfty
  push_neg at hInfty
  cases' hInfty with finA finB
  wlog cAB : IsCompact A ∧ IsCompact B with goal_cpt
  · apply le_of_forall_pos_lt_add'
    intros ε hε
    have hε' : (ε/2) ≠ 0 := by exact ENNReal_div_two_ne_zero ε hε
    obtain ⟨Aε, inclusion_cptA, nonempty_cptA, h_cptA, diff_cptA⟩ := MeasurableSet.exists_isCompact_Nonempty_diff_lt hA mA finA hε'
    obtain ⟨Bε, inclusion_cptB, nonempty_cptB, h_cptB, diff_cptB⟩ := MeasurableSet.exists_isCompact_Nonempty_diff_lt hB mB finB hε'

    have mAε : MeasurableSet Aε := IsCompact.measurableSet h_cptA
    have mBε : MeasurableSet Bε := IsCompact.measurableSet h_cptB

    have finAε : volume Aε ≠ ⊤ := volume_ne_top_of_subset A finA inclusion_cptA
    have finBε : volume Bε ≠ ⊤ := volume_ne_top_of_subset B finB inclusion_cptB

    have diff_cptA' : volume A < volume Aε + ε/2 := volume_lt_subset_add_diff A mAε finAε inclusion_cptA diff_cptA
    have diff_cptB' : volume B < volume Bε + ε/2 := volume_lt_subset_add_diff B mBε finBε inclusion_cptB diff_cptB

    have wma_cpt : volume Aε + volume Bε ≤ volume C := by
      have inclusion_cpt : Aε + Bε ⊆ C := subset_add_subset_subset A B h inclusion_cptA inclusion_cptB
      have feather : IsCompact Aε ∧ IsCompact Bε := And.intro h_cptA h_cptB
      exact goal_cpt Aε Bε C nonempty_cptA nonempty_cptB hC mAε mBε mC inclusion_cpt finAε finBε feather

    calc volume A + volume B < volume Aε + ε/2 + (volume Bε + ε/2) := ENNReal.add_lt_add diff_cptA' diff_cptB'
    _ = volume Aε + volume Bε + ε := add_with_halves_eq_one (volume Aε) (volume Bε) ε
    _ ≤  volume C + ε := add_le_add_right wma_cpt ε

  obtain ⟨cA, cB⟩ := cAB
  exact one_dim_BMInequality_cpt A B C hA hB mB h cA cB
