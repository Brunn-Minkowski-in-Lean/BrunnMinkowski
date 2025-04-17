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
    ∫ (y : ι → ℝ), f ((MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) e) y) =
    ∫ (x : κ → ℝ), f x := by
  apply MeasurePreserving.integral_comp _
    (MeasurableEquiv.measurableEmbedding (MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) e))
  apply volume_measurePreserving_piCongrLeft

theorem helper_lemma₄ (f : ((ι ⊕ κ) → ℝ) → ℝ) :
    ∫ (x : (ι ⊕ κ) → ℝ), f x =
    ∫ (y : (ι → ℝ) × (κ → ℝ)), f ((MeasurableEquiv.sumPiEquivProdPi fun _ : ι ⊕ κ ↦ ℝ).symm y) := by
  symm; apply MeasurePreserving.integral_comp
  · exact volume_measurePreserving_sumPiEquivProdPi_symm _
  · exact MeasurableEquiv.measurableEmbedding _

theorem helper_lemma₅ (f : (ι ⊕ κ → ℝ) → ℝ) :
    Integrable f ↔
    Integrable (f ∘ (MeasurableEquiv.sumPiEquivProdPi fun _ : ι ⊕ κ ↦ ℝ).symm) := by
  rw [← MeasurableEmbedding.integrable_map_iff
    (MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ).symm.measurableEmbedding,
    (volume_measurePreserving_sumPiEquivProdPi_symm fun _ : ι ⊕ κ ↦ ℝ).map_eq]

theorem helper_lemma₆ (h : ι ≃ κ) (f : (ι → ℝ) → ℝ) :
    Integrable f ↔
    Integrable (f ∘ (MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) h).symm) := by
  rw [← MeasurableEmbedding.integrable_map_iff
    (MeasurableEquiv.measurableEmbedding (MeasurableEquiv.piCongrLeft (fun x ↦ ℝ) h).symm)]
  have := (volume_measurePreserving_piCongrLeft (fun _ ↦ ℝ) h).symm
  rw [this.map_eq]

  theorem helper_lemma₆' (h : ι ≃ κ) (f : (ι → ℝ) → ℝ) :
    Integrable f ↔
    Integrable (f ∘ (MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) h.symm)) := by
  rw [← MeasurableEmbedding.integrable_map_iff
    (MeasurableEquiv.measurableEmbedding (MeasurableEquiv.piCongrLeft (fun x ↦ ℝ) h.symm))]
  have := (volume_measurePreserving_piCongrLeft (fun _ ↦ ℝ) h.symm)
  rw [this.map_eq]

universe u in
def helper_def₁ {ι : Type u} {n m : ℕ} (h : ι ≃ Fin n ⊕ Fin m) :
    ι ≃ (ULift.{u} (Fin n)) ⊕ (ULift.{u} (Fin m)) where
  toFun i := match h i with | .inl x => .inl ⟨x⟩ | .inr x => .inr ⟨x⟩
  invFun x := match x with | .inl x => h.symm (.inl x.down) | .inr x => h.symm (.inr x.down)
  left_inv i := by
    match v : h i with
    | .inl x => simp_rw [v, ← v, Equiv.symm_apply_apply]
    | .inr x => simp_rw [v, ← v, Equiv.symm_apply_apply]
  right_inv x := by match x with | .inl x => simp | .inr x => simp

universe u in
theorem helper_lemma₇
    {ι : Type u} [Fintype ι] {κ₁ : Type u} [Fintype κ₁] {κ₂ : Type u} [Fintype κ₂]
    (h : ι ≃ κ₁ ⊕ κ₂) {f : EuclideanSpace ℝ ι → ℝ} (hf : Integrable f (volume : Measure (ι → ℝ))) :
    Integrable fun x ↦ ∫ (y : κ₂ → ℝ), f
      ((MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) h).symm
        ((MeasurableEquiv.sumPiEquivProdPi _).symm (x, y))) := by
  simp_rw [← @Function.comp_apply _ _ _ f, ← @Function.comp_apply _ _ _ (f ∘ _),
    ← @Function.comp_apply _ _ _ _ (Prod.mk _)]
  apply Integrable.integral_prod_left ((helper_lemma₅ _).mp _)
  rwa [← helper_lemma₆]


universe u in
theorem helper_lemma₈
    {ι : Type u} {κ₁ : Type u} {κ₂ : Type u} [Fintype κ₂] (h : ι ≃ κ₁ ⊕ κ₂)
    {f : EuclideanSpace ℝ ι → ℝ} (hf : 0 ≤ f) :
    0 ≤ fun x ↦ ∫ (y : κ₂ → ℝ), f
      ((MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) h).symm
        ((MeasurableEquiv.sumPiEquivProdPi _).symm (x, y))) := by
  intro; simp; apply integral_nonneg; tauto

theorem le_of_eq_of_le_of_eq {α : Type*} [LE α] {a b c d : α}
    (hab : a = b) (hbc : b ≤ c) (hcd : c = d) : a ≤ d :=
  hab ▸ hcd ▸ hbc

universe u in
theorem prekopa_leindler'
    {ι : Type u} [Fintype ι]
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
    have h₂ := helper_def₁ ((h₁ ▸ Fintype.equivFin ι).trans finSumFinEquiv.symm)
    rw [← Fintype.card_fin n, ← Fintype.card_fin m]
    simp_rw [← helper_lemma₃ h₂.symm, helper_lemma₄, Measure.volume_eq_prod]
    rw [integral_prod, integral_prod, integral_prod]
    · let F : (ULift.{u} (Fin n) → ℝ) → ℝ := fun x ↦ ∫ (y : ULift.{u} (Fin m) → ℝ), f
        ((MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) h₂).symm
          ((MeasurableEquiv.sumPiEquivProdPi _).symm (x, y)))
      have hF₁ : Integrable F := helper_lemma₇ h₂ hf₁
      have hF₂ : 0 ≤ F := helper_lemma₈ h₂ hf₂
      let G : (ULift.{u} (Fin n) → ℝ) → ℝ := fun x ↦ ∫ (y : ULift.{u} (Fin m) → ℝ), g
        ((MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) h₂).symm
          ((MeasurableEquiv.sumPiEquivProdPi _).symm (x, y)))
      have hG₁ : Integrable G := helper_lemma₇ h₂ hg₁
      have hG₂ : 0 ≤ G := helper_lemma₈ h₂ hg₂
      let H : (ULift.{u} (Fin n) → ℝ) → ℝ := fun x ↦
        (1 - t) ^ ((1 - t) * m) *
        t ^ (t * m) *
        ∫ (y : ULift.{u} (Fin m) → ℝ), h
          ((MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) h₂).symm
            ((MeasurableEquiv.sumPiEquivProdPi _).symm (x, y)))
      have hH₁ : Integrable H := Integrable.const_mul (helper_lemma₇ h₂ hh₁) _
      have h₃ := hn ((helper_lemma₂ _).mpr hF₁) hF₂ ((helper_lemma₂ _).mpr hG₁) hG₂
        ((helper_lemma₂ _).mpr hH₁) ?_ (by simp)
      -- have h₃ : ∀ {x y}, (F x) ^ (1 - t) * (G y) ^ t ≤ H (x + y) := by
      --   sorry
        -- simp [F, G, H]
        -- intro x y
        -- simp_rw [← @Function.comp_apply _ _ _ f, ← @Function.comp_apply _ _ _ g,
        --   ← @Function.comp_apply _ _ _ h, ← @Function.comp_apply _ _ _ (_ ∘ _),
        --   @Function.comp_apply _ _ _ _ (Prod.mk _)]
        -- simp_rw [← @Prod.swap_prod_mk _ _ _ x, ← @Prod.swap_prod_mk _ _ _ y,
        --   ← @Prod.swap_prod_mk _ _ _ (x + y)]
        -- simp_rw [← @Function.comp_apply _ _ _ Prod.swap, ← @Function.comp_apply _ _ _ _ (_ ∘ _)]
        -- sorry
      -- have h₄ := hn ((helper_lemma₂ _).mpr hF₁) hF₂ ((helper_lemma₂ _).mpr hG₁) hG₂
      --   ((helper_lemma₂ _).mpr hH₁) h₃ (by simp)
      rw [integral_integral, integral_integral, integral_integral] at *
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
    all_goals (refine (integrable_prod_iff ?_).mpr ⟨?_, ?_⟩)
    · let p₁:= (helper_lemma₆' h₂ h).mp hh₁;
      let p₂:= (helper_lemma₅ _ ).mp p₁;
      simp [Function.comp] at p₂
      simp [Integrable] at p₂
      exact (And.left p₂)

    · let p₁:= (helper_lemma₆' h₂ h).mp hh₁;
      let p₂:= (helper_lemma₅ _ ).mp p₁;
      let p₃:= (MeasureTheory.Integrable.prod_right_ae p₂);
      simp [Function.comp] at p₃
      exact p₃

    · let p₁:= (helper_lemma₆' h₂ h).mp hh₁;
      let p₂:= (helper_lemma₅ _ ).mp p₁;
      let p₃:= MeasureTheory.Integrable.norm p₂;
      let p₄:= Integrable.integral_prod_left p₃;
      simp [Function.comp] at p₄
      exact p₄

    · let p₁:= (helper_lemma₆' h₂ g).mp hg₁;
      let p₂:= (helper_lemma₅ _ ).mp p₁;
      simp [Function.comp] at p₂
      simp [Integrable] at p₂
      exact (And.left p₂)

    · let p₁:= (helper_lemma₆' h₂ g).mp hg₁;
      let p₂:= (helper_lemma₅ _ ).mp p₁;
      let p₃:= (MeasureTheory.Integrable.prod_right_ae p₂);
      simp [Function.comp] at p₃
      exact p₃

    · let p₁:= (helper_lemma₆' h₂ g).mp hg₁;
      let p₂:= (helper_lemma₅ _ ).mp p₁;
      let p₃:= MeasureTheory.Integrable.norm p₂;
      let p₄:= Integrable.integral_prod_left p₃;
      simp [Function.comp] at p₄
      exact p₄

    · let p₁:= (helper_lemma₆' h₂ f).mp hf₁;
      let p₂:= (helper_lemma₅ _ ).mp p₁;
      simp [Function.comp] at p₂
      simp [Integrable] at p₂
      exact (And.left p₂)

    · let p₁:= (helper_lemma₆' h₂ f).mp hf₁;
      let p₂:= (helper_lemma₅ _ ).mp p₁;
      let p₃:= (MeasureTheory.Integrable.prod_right_ae p₂);
      simp [Function.comp] at p₃
      exact p₃

    · let p₁:= (helper_lemma₆' h₂ f).mp hf₁;
      let p₂:= (helper_lemma₅ _ ).mp p₁;
      let p₃:= MeasureTheory.Integrable.norm p₂;
      let p₄:= Integrable.integral_prod_left p₃;
      simp [Function.comp] at p₄
      exact p₄


end
