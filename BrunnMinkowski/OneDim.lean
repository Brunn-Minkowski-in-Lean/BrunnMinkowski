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
  obtain ⟨b, hb⟩ := hB -- hB is a pair of b and proof of b in B
  calc
    volume A = volume (A + {b}) := by
      rw [add_singleton, image_add_right,
      measure_preimage_add_right]
    _ ≤ volume (A + B) := by
      apply measure_mono
      apply add_subset_add_left
      exact singleton_subset_iff.mpr hb

lemma volume_le_volume_add_left
    {A B : Set ℝ} (hB : B.Nonempty)
    : volume A ≤ volume (B + A) := by
  rw [addCommMonoid.proof_1 B]
  exact volume_le_volume_add_right hB

lemma measure_diff_singleton_lt {α : Type} [MeasurableSpace α] (μ : Measure α) (A : Set α) (a : α) : μ (A \ {a}) ≤ μ A := by
  simp only [diff_subset, measure_mono]

lemma MeasurableSet.exists_isCompact_Nonempty_diff_lt
    {α : Type} [MeasurableSpace α] {μ : Measure α} [TopologicalSpace α]
    [OpensMeasurableSpace α] [T2Space α] [μ.InnerRegularCompactLTTop]
    {A : Set α} (hA : A.Nonempty) (mA : MeasurableSet A) (h'A : μ A ≠ ⊤)
    {ε : ENNReal} (hε : ε ≠ 0) : ∃ K ⊆ A, K.Nonempty ∧ IsCompact K ∧ μ (A \ K) < ε := by
  obtain ⟨K_tilde, inclusion_K_tilde, cpt_K_tilde, diff_K_tilde⟩ := mA.exists_isCompact_diff_lt h'A hε
  by_cases nonempty_K_tilde : K_tilde.Nonempty
  · -- K_tilde is nonempty : Take K = K_tilde
    exact ⟨K_tilde, inclusion_K_tilde, nonempty_K_tilde, cpt_K_tilde, diff_K_tilde⟩
  · -- K_tilde is empty
    obtain ⟨a, ha⟩ := hA
    use {a} -- Take K = {a}
    constructor
    · -- {a} ⊆ A
      exact singleton_subset_iff.mpr ha
    · constructor
      · -- {a} is nonempty
        exact singleton_nonempty a
      · constructor
        · -- {a} is cpt
          exact isCompact_singleton
        · -- μ (A \ {a}) ≤ μ A
          have small_A : μ A < ε := by
            push_neg at nonempty_K_tilde
            rw [nonempty_K_tilde, diff_empty] at diff_K_tilde
            exact diff_K_tilde
          calc
            μ (A \ {a}) ≤ μ A := by exact measure_diff_singleton_lt μ A a
            _ < ε := by exact small_A

lemma one_dim_BMInequality_infty (A B C : Set ℝ)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (h : A + B ⊆ C) (hInfty: volume A = ⊤ ∨ volume B = ⊤)
    : volume A + volume B ≤ volume C := by
      cases' hInfty with hInfty_A hInfty_B
      rw [hInfty_A, _root_.top_add, ← hInfty_A]
      apply le_trans
        (volume_le_volume_add_right hB)
        (measure_mono h)
      rw [hInfty_B, _root_.add_top, ← hInfty_B]
      apply le_trans
        (volume_le_volume_add_left hA)
        (measure_mono h)

lemma ENNReal_div_two_ne_zero (ε : ENNReal) (hε : 0 < ε) : (ε/2) ≠ 0 := by
  by_contra he
  have he : ε = 0 := by
    rw [ENNReal.div_eq_zero_iff] at he
    cases' he with zero_ε two_eq_top
    · exact zero_ε
    · contradiction
    -- simp_all only [and_imp, not_and, ENNReal.ofNat_ne_top, or_false]
  rw [he, lt_self_iff_false] at hε
  exact hε

lemma volume_ne_top_of_subset (finA : volume A ≠ ⊤) (h : Aε ⊆ A) : volume Aε ≠ ⊤ := by
  by_contra inftyAε
  have feather : volume Aε ≤ volume A := by exact measure_mono h
  rw [inftyAε, top_le_iff] at feather
  contradiction

lemma volume_lt_subset_add_diff (mAε : MeasurableSet Aε) (finAε : volume Aε ≠ ⊤) (h : Aε ⊆ A) (diff : volume (A \ Aε) < ε / 2) : volume A < volume Aε + ε/2 := by
  have feather1 : volume A = volume Aε + volume (A\Aε) := by
    have feather2 : volume (A ∩ Aε) + volume (A \ Aε) = volume A := by apply measure_inter_add_diff A mAε
    have feather3 : volume (A ∩ Aε) = volume Aε := by rw [inter_eq_right.mpr h]
    calc volume A = volume (A ∩ Aε) + volume (A \ Aε) := by rw [←feather2]
      _ = volume Aε + volume (A \ Aε) := by rw [feather3]
  calc volume A = volume Aε + volume (A \ Aε) := by apply feather1
  _ < volume Aε + ε/2 := by exact ENNReal.add_lt_add_left finAε diff

lemma subset_add_subset_subset (h : A + B ⊆ C) (hInclA : Aε ⊆ A) (hInclB : Bε ⊆ B) : Aε + Bε ⊆ C := by
  have feather : Aε + Bε ⊆ A + B := by
    intros x hx
    have hx' : ∃ a ∈ Aε, ∃ b ∈ Bε, a + b = x := by exact mem_add.mpr hx
    obtain ⟨a, ha, b, hb, hx'⟩ := hx'
    have ha : a ∈ A := by exact hInclA ha
    have hb : b ∈ B := by exact hInclB hb
    have h : a + b ∈ A + B := by apply add_mem_add ha hb
    rw [← hx']
    exact h
  calc Aε + Bε ⊆ A + B := by apply feather
    _ ⊆ C := by apply h

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

lemma inter_sInf_sSup_eq_singleton (hA : A.Nonempty) (hB : B.Nonempty) (cA : IsCompact A) (cB : IsCompact B)
  (hAt : At = sInf B +ᵥ A) (hBt : Bt = sSup A +ᵥ B) : At ∩ Bt = {sSup A + sInf B} := by
  rw [Set.ext_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨xAt, xBt⟩ := hx
    rw [hAt] at xAt
    apply mem_vadd_set.mp at xAt
    cases' xAt with a ha
    obtain ⟨ha, hax⟩ := ha
    rw [hBt] at xBt
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
      subst hbx
      rw [vadd_eq_add, add_le_add_iff_left]
      exact infB_le_b
    rw [add_comm] at upper_x
    exact le_antisymm upper_x lower_x
  · intro hx
    apply mem_singleton_iff.mp at hx
    constructor
    · have x_At : sSup A + sInf B ∈ sInf B +ᵥ A := by
        have supA_A : sSup A ∈ A := by exact IsCompact.sSup_mem cA hA
        rw [add_comm]
        apply vadd_mem_vadd_set_iff.mpr
        exact supA_A
      simp only [hx, hAt, x_At]
    · have x_Bt : sSup A  + sInf B ∈ sSup A +ᵥ B := by
        have infB_B : sInf B ∈ B := by exact IsCompact.sInf_mem cB hB
        apply vadd_mem_vadd_set_iff.mpr
        exact infB_B
      simp only [hx, hBt, x_Bt]

lemma test3 (h : MeasurableSet B): volume (A ∪ B) + volume (A ∩ B) = volume A + volume B := by
  exact measure_union_add_inter A h

lemma one_dim_BMInequality_fin_cpt (A B C : Set ℝ)
    (hA : A.Nonempty) (hB : B.Nonempty) (mB : MeasurableSet B)
    (h : A + B ⊆ C)
    (cA : IsCompact A) (cB : IsCompact B)
    : volume A + volume B ≤ volume C := by

  set At := sInf B +ᵥ A with eq_At
  set Bt := sSup A +ᵥ B with eq_Bt

  have eq_At_vol : volume At = volume A := by exact measure_translation_of_set A (sInf B)
  have eq_Bt_vol : volume Bt = volume B := by exact measure_translation_of_set B (sSup A)

  have cup_At_Bt : At ∪ Bt ⊆ C := by
    have sub_At : At ⊆ C := by exact sInf_of_cpt_vadd_subset A B h hB cB
    have sub_Bt : Bt ⊆ C := by exact sSup_of_cpt_vadd_subset A B h hA cA
    exact union_subset_iff.mpr ⟨sub_At, sub_Bt⟩

  have m_zero_AtBt : volume (At ∩ Bt) = 0 := by
    have cap_At_Bt : At ∩ Bt = {sSup A + sInf B} := by exact inter_sInf_sSup_eq_singleton A B hA hB cA cB eq_At eq_Bt
    calc volume (At ∩ Bt) = volume {sSup A + sInf B} := by rw [cap_At_Bt]
    _ = 0 := by rw [Real.volume_singleton]

  calc volume A + volume B = volume At + volume Bt - 0 := by rw [eq_At_vol, eq_Bt_vol, tsub_zero]
  _ = volume At + volume Bt - volume (At ∩ Bt) := by rw [← m_zero_AtBt]
  _ = volume (At ∪ Bt) := by
    have vol_union_AtBt : volume (At ∪ Bt) + volume (At ∩ Bt) = volume At + volume Bt := by exact test3 At Bt (MeasurableSet.const_vadd mB (sSup A))
    have m_not_top_AtBt : volume (At ∩ Bt) ≠ ⊤ := by
      by_contra feather
      rw [m_zero_AtBt] at feather
      contradiction
    rw [←vol_union_AtBt, add_comm, ENNReal.add_sub_cancel_left]
    exact m_not_top_AtBt
  _ ≤ volume C := by exact measure_mono cup_At_Bt

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
  · -- Prove non-cpt A, B case assuming cpt A, B case
    apply le_of_forall_pos_lt_add'
    intros ε hε
    have hε' : (ε/2) ≠ 0 := by exact ENNReal_div_two_ne_zero ε hε
    obtain ⟨Aε, inclusion_cptA, nonempty_cptA, h_cptA, diff_cptA⟩ :=
      MeasurableSet.exists_isCompact_Nonempty_diff_lt hA mA finA hε'
    obtain ⟨Bε, inclusion_cptB, nonempty_cptB, h_cptB, diff_cptB⟩ :=
      MeasurableSet.exists_isCompact_Nonempty_diff_lt hB mB finB hε'

    have mAε : MeasurableSet Aε := by exact IsCompact.measurableSet h_cptA
    have mBε : MeasurableSet Bε := by exact IsCompact.measurableSet h_cptB

    have finAε : volume Aε ≠ ⊤ := by exact volume_ne_top_of_subset A finA inclusion_cptA
    have finBε : volume Bε ≠ ⊤ := by exact volume_ne_top_of_subset B finB inclusion_cptB

    have diff_cptA' : volume A < volume Aε + ε/2 := by exact volume_lt_subset_add_diff A mAε finAε inclusion_cptA diff_cptA
    have diff_cptB' : volume B < volume Bε + ε/2 := by exact volume_lt_subset_add_diff B mBε finBε inclusion_cptB diff_cptB

    have wma_cpt : volume Aε + volume Bε ≤ volume C := by
      have inclusion_cpt : Aε + Bε ⊆ C := by exact subset_add_subset_subset A B h inclusion_cptA inclusion_cptB
      have feather : IsCompact Aε ∧ IsCompact Bε := by apply And.intro h_cptA h_cptB
      exact goal_cpt Aε Bε C nonempty_cptA nonempty_cptB hC mAε mBε mC inclusion_cpt finAε finBε feather

    calc volume A + volume B < volume Aε + ε/2 + (volume Bε + ε/2) := by exact ENNReal.add_lt_add diff_cptA' diff_cptB'
    _ = volume Aε + volume Bε + ε := by exact add_with_halves_eq_one (volume Aε) (volume Bε) ε
    _ ≤  volume C + ε := by exact add_le_add_right wma_cpt ε

  -- Prove the theorem assuming cpt A, B
  obtain ⟨cA, cB⟩ := cAB
  exact one_dim_BMInequality_fin_cpt A B C hA hB mB h cA cB
