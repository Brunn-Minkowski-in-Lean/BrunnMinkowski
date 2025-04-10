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
    (hι : {f : (ι → ℝ) → ℝ} → Integrable f → 0 ≤ f →
          {g : (ι → ℝ) → ℝ} → Integrable g → 0 ≤ g →
          {h : (ι → ℝ) → ℝ} → Integrable h →
          (∀ {x y}, (f x) ^ (1 - t) * (g y) ^ t ≤ h (x + y)) →
          (∫ x, f x) ^ (1 - t) * (∫ y, g y) ^ t ≤
          (1 - t) ^ ((1 - t) * Fintype.card ι) * t ^ (t * Fintype.card ι) * (∫ z, h z))
    (hκ : {f : (κ → ℝ) → ℝ} → Integrable f → 0 ≤ f →
          {g : (κ → ℝ) → ℝ} → Integrable g → 0 ≤ g →
          {h : (κ → ℝ) → ℝ} → Integrable h →
          (∀ {x y}, (f x) ^ (1 - t) * (g y) ^ t ≤ h (x + y)) →
          (∫ x, f x) ^ (1 - t) * (∫ y, g y) ^ t ≤
          (1 - t) ^ ((1 - t) * Fintype.card κ) * t ^ (t * Fintype.card κ) * (∫ z, h z))
    {f : ((ι ⊕ κ) → ℝ) → ℝ} (hf₁ : Integrable f) (hf₂ : 0 ≤ f)
    {g : ((ι ⊕ κ) → ℝ) → ℝ} (hg₁ : Integrable g) (hg₂ : 0 ≤ g)
    {h : ((ι ⊕ κ) → ℝ) → ℝ} (hh₁ : Integrable h)
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

theorem helper_lemma₃ (e : ι ≃ κ) (f : (κ → ℝ) → ℝ) :
    ∫ (y : ι → ℝ), f ((MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl ℝ)) y) =
    ∫ (x : κ → ℝ), f x := by
  apply MeasurePreserving.integral_comp _
    (MeasurableEquiv.measurableEmbedding (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl ℝ)))
  apply measurePreserving_arrowCongr'
  simp [MeasurableEquiv.refl, MeasurePreserving.id]

theorem helper_lemma₄ (f : ((ι ⊕ κ) → ℝ) → ℝ) :
    ∫ (x : (ι ⊕ κ) → ℝ), f x =
    ∫ (y : (ι → ℝ) × (κ → ℝ)), f ((Equiv.sumArrowEquivProdArrow _ _ ℝ).symm y) := by
  symm; apply MeasurePreserving.integral_comp
  · sorry
  · sorry

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
    rw [helper_lemma₂] at hf₁ hg₁ hh₁
    simp only [EuclideanSpace, PiLp, WithLp] at f g h hn hm h₀
    have h₂ := (h₁ ▸ Fintype.equivFin ι).trans finSumFinEquiv.symm
    have h₃ := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ h₂
    rw [← Fintype.card_fin n, ← Fintype.card_fin m]
    simp_rw [← helper_lemma₃ h₂.symm]
    let F : (Fin n → ℝ) → ℝ := fun x ↦ ∫ (y : Fin m → ℝ), f
      ((MeasurableEquiv.arrowCongr' h₂ (MeasurableEquiv.refl ℝ)).symm
        ((Equiv.sumArrowEquivProdArrow _ _ ℝ).symm (x, y)))
    let G : (Fin n → ℝ) → ℝ := fun x ↦ ∫ (y : Fin m → ℝ), g
      ((MeasurableEquiv.arrowCongr' h₂ (MeasurableEquiv.refl ℝ)).symm
        ((Equiv.sumArrowEquivProdArrow _ _ ℝ).symm (x, y)))
    let H : (Fin n → ℝ) → ℝ := fun x ↦ ∫ (y : Fin m → ℝ), h
      ((MeasurableEquiv.arrowCongr' h₂ (MeasurableEquiv.refl ℝ)).symm
        ((Equiv.sumArrowEquivProdArrow _ _ ℝ).symm (x, y)))
    sorry

end
