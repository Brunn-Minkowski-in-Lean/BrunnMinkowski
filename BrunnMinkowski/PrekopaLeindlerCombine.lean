import Mathlib

import BrunnMinkowski.PrekopaLeindler

section

open MeasureTheory

variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]

theorem Nat.induction_on_add
    {p : ℕ → Prop} (n : ℕ) (hzero : p 0) (hone : p 1)
    (hadd : ∀ ⦃n⦄, p n → ∀ ⦃m⦄, p m → p (n + m)) :
    p n := by
  induction n <;> simp_all only

@[simp]
theorem volume_univ_eq_of_pi_empty {α : Type*} [Fintype α] [IsEmpty α] :
    volume (@Set.univ (α → ℝ)) = 1 := by
  simp only [volume_pi, Measure.pi_empty_univ]

@[simp]
theorem EuclideanSpace.volume_univ_eq_one_of_rank_zero {ι : Type*} [Fintype ι] [IsEmpty ι] :
    volume (@Set.univ (EuclideanSpace ℝ ι))= 1 := by
  simp only [volume_euclideanSpace_eq_dirac, measure_univ]

@[simp]
theorem EuclideanSpace.integral_of_empty_eq_one
    {ι : Type*} [Fintype ι] [IsEmpty ι] (f : EuclideanSpace ℝ ι → ℝ) :
    ∫ (x : EuclideanSpace ℝ ι), f x = f 0 := by
  simp [integral_unique, default, isEmptyElim]
  congr; funext; rw [PiLp.zero_apply]; tauto

theorem prekopa_leindler
    {t : ℝ} (ht₁ : 0 < t) (ht₂ : t < 1) {d : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf₁ : 0 ≤ f) (hf₂ : Integrable f) 
    {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg₁ : 0 ≤ g) (hg₂ : Integrable g)
    {h : EuclideanSpace ℝ (Fin d) → ℝ} (hh₁ : 0 ≤ h) (hh₂ : Integrable h)
    (h₀ : ∀ x y, (f x) ^ (1 - t) * (g y) ^ t ≤ h (x + y)) :
    (∫ x, f x) ^ (1 - t) * (∫ y, g y) ^ t ≤
    (1 - t) ^ (d * (1 - t)) * t ^ (d * t) * (∫ z, h z) := by
  sorry

theorem prekopa_leindler_add
    {t : ℝ} (ht₁ : 0 < t) (ht₂ : t < 1)
    (hι : {f : EuclideanSpace ℝ ι → ℝ} → Integrable f → 0 ≤ f →
          {g : EuclideanSpace ℝ ι → ℝ} → Integrable g → 0 ≤ g →
          {h : EuclideanSpace ℝ ι → ℝ} → Integrable h →
          (∀ {x y}, (f x) ^ (1 - t) * (g y) ^ t ≤ h (x + y)) →
          (∫ x, f x) ^ (1 - t) * (∫ y, g y) ^ t ≤
          (1 - t) ^ ((1 - t) * Fintype.card ι) * t ^ (t * Fintype.card ι) * (∫ z, h z))
    (hκ : {f : EuclideanSpace ℝ κ → ℝ} → Integrable f → 0 ≤ f →
          {g : EuclideanSpace ℝ κ → ℝ} → Integrable g → 0 ≤ g →
          {h : EuclideanSpace ℝ κ → ℝ} → Integrable h →
          (∀ {x y}, (f x) ^ (1 - t) * (g y) ^ t ≤ h (x + y)) →
          (∫ x, f x) ^ (1 - t) * (∫ y, g y) ^ t ≤
          (1 - t) ^ ((1 - t) * Fintype.card κ) * t ^ (t * Fintype.card κ) * (∫ z, h z))
    {f : EuclideanSpace ℝ (ι ⊕ κ) → ℝ} (hf₁ : Integrable f) (hf₂ : 0 ≤ f)
    {g : EuclideanSpace ℝ (ι ⊕ κ) → ℝ} (hg₁ : Integrable g) (hg₂ : 0 ≤ g)
    {h : EuclideanSpace ℝ (ι ⊕ κ) → ℝ} (hh₁ : Integrable h)
    (h₀ : ∀ {x y}, (f x) ^ (1 - t) * (g y) ^ t ≤ h (x + y)) :
    (∫ x, f x) ^ (1 - t) * (∫ y, f y) ^ t ≤
    (1 - t) ^ ((1 - t) * (Fintype.card ι + Fintype.card κ)) *
    t ^ (t * (Fintype.card ι + Fintype.card κ)) * (∫ z, h z) := by
  sorry

theorem helper_lemma₁ (f : EuclideanSpace ℝ ι → ℝ) :
    ∫ (x : EuclideanSpace ℝ ι), f x = ∫ (x : ι → ℝ), f x := by
  have := MeasurePreserving.integral_comp
    (EuclideanSpace.volume_preserving_measurableEquiv ι).symm
    (MeasurableEquiv.measurableEmbedding (EuclideanSpace.measurableEquiv ι).symm) f
  rw [← this]; rfl

theorem helper_lemma₂ (f : EuclideanSpace ℝ ι → ℝ) :
    Integrable f (volume : Measure (EuclideanSpace ℝ ι)) ↔
    Integrable f (volume : Measure (ι → ℝ)) := by
  rw [← MeasurePreserving.integrable_comp_emb
    (EuclideanSpace.volume_preserving_measurableEquiv ι)
    (MeasurableEquiv.measurableEmbedding (EuclideanSpace.measurableEquiv ι))]
  rfl

theorem prekopa_leindler'
    {t : ℝ} (ht₁ : 0 < t) (ht₂ : t < 1)
    {f : EuclideanSpace ℝ ι → ℝ} (hf₁ : Integrable f) (hf₂ : 0 ≤ f)
    {g : EuclideanSpace ℝ ι → ℝ} (hg₁ : Integrable g) (hg₂ : 0 ≤ g)
    {h : EuclideanSpace ℝ ι → ℝ} (hh₁ : Integrable h)
    (h₀ : ∀ {x y}, (f x) ^ (1 - t) * (g y) ^ t ≤ h (x + y)) :
    (∫ x, f x) ^ (1 - t) * (∫ y, g y) ^ t ≤
    (1 - t) ^ ((1 - t) * Fintype.card ι) * t ^ (t * Fintype.card ι) * (∫ z, h z) := by
  induction h₁ : Fintype.card ι using Nat.induction_on_add generalizing ι
  case hzero =>
    rw [Fintype.card_eq_zero_iff] at h₁
    simp [h₁]
    nth_rw 3 [← add_zero 0]
    exact h₀
  case hone => sorry
  case hadd n hn m hm i =>
    simp_rw [helper_lemma₁ f, helper_lemma₁ g, helper_lemma₁ h]
    simp_rw [helper_lemma₁, helper_lemma₂, EuclideanSpace, PiLp, WithLp] at *
    sorry

end
