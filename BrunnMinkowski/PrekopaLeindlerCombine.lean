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
    volume (@Set.univ (EuclideanSpace ℝ ι)) = 1 := by
  simp only [volume_euclideanSpace_eq_dirac, measure_univ]

@[simp]
theorem EuclideanSpace.volume_real_univ_eq_one_of_rank_zero {ι : Type*} [Fintype ι] [IsEmpty ι] :
    volume.real (@Set.univ (EuclideanSpace ℝ ι)) = 1 := by
  simp only [measureReal_def, volume_univ_eq_one_of_rank_zero, ENNReal.toReal_one]

instance EuclideanSpace.instUnique {𝕜 ι : Type*} [Fintype ι] [IsEmpty ι] :
    Unique (EuclideanSpace 𝕜 ι) :=
  Pi.uniqueOfIsEmpty _

@[simp]
theorem EuclideanSpace.integral_of_empty_eq_one
    {ι : Type*} [Fintype ι] [IsEmpty ι] (f : EuclideanSpace ℝ ι → ℝ) :
    ∫ (x : EuclideanSpace ℝ ι), f x = f 0 := by
  simp [integral_unique, default, isEmptyElim]
  congr; funext; simp only [PiLp.zero_apply]; tauto

theorem _root_.ENNReal.ofReal_rpow {p : ℝ} (hp : 0 ≤ p) {r : ℝ} (hr : 0 ≤ r):
    ENNReal.ofReal (p ^ r) = ENNReal.ofReal p ^ r :=
  (ENNReal.ofReal_rpow_of_nonneg hp hr).symm

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

theorem helper_lemma₁' (f : (ι → ℝ) → ℝ) :
    ∫ (x : EuclideanSpace ℝ ι), f x = ∫ (x : ι → ℝ), f x :=
  helper_lemma₁ f

theorem helper_lemma₁'' (f : EuclideanSpace ℝ ι → ENNReal) :
    ∫⁻ x, f x = ∫⁻ (x : ι → ℝ), f x ∂(volume : Measure (ι → ℝ)) := by
  apply MeasurePreserving.lintegral_comp_emb
  · rw [← (EuclideanSpace.volume_preserving_measurableEquiv ι).map_eq]; tauto
  · exact Measurable.measurableEmbedding (fun ⦃_⦄ ↦ id) fun ⦃_ _⦄ ↦ id

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

theorem helper_lemma₃' (e : ι ≃ κ) (f : (κ → ℝ) → ENNReal) :
    ∫⁻ (y : ι → ℝ), f ((MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) e) y) =
    ∫⁻ (x : κ → ℝ), f x :=
  MeasurePreserving.lintegral_comp_emb
    (volume_measurePreserving_piCongrLeft (fun _ ↦ ℝ) e)
    (MeasurableEquiv.measurableEmbedding (MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) e)) _

theorem helper_lemma₄ (f : ((ι ⊕ κ) → ℝ) → ℝ) :
    ∫ (x : (ι ⊕ κ) → ℝ), f x =
    ∫ (y : (ι → ℝ) × (κ → ℝ)), f ((MeasurableEquiv.sumPiEquivProdPi fun _ : ι ⊕ κ ↦ ℝ).symm y) := by
  symm; apply MeasurePreserving.integral_comp
  · exact volume_measurePreserving_sumPiEquivProdPi_symm _
  · exact MeasurableEquiv.measurableEmbedding _

theorem helper_lemma₄' (f : ((ι ⊕ κ) → ℝ) → ENNReal) :
    ∫⁻ (x : ι ⊕ κ → ℝ), f x =
    ∫⁻ (y : (ι → ℝ) × (κ → ℝ)), f ((MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ).symm y) :=
  (MeasurePreserving.lintegral_comp_emb (volume_measurePreserving_sumPiEquivProdPi_symm fun _ ↦ ℝ)
    (MeasurableEquiv.measurableEmbedding (MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ).symm) _).symm

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

theorem uncurry_prod_swap {α β γ : Type*} (f : α × β → γ) :
    (Function.uncurry fun x y ↦ f (y, x)) = f ∘ Prod.swap :=
  rfl

/- TODO: in mathlib -/
def LinearIsometryEquiv.prodComm
    (R : Type*) [Semiring R]
    (E₁ : Type*) [SeminormedAddCommGroup E₁] [Module R E₁]
    (E₂ : Type*) [SeminormedAddCommGroup E₂] [Module R E₂] :
    E₁ × E₂ ≃ₗᵢ[R] E₂ × E₁ :=
  ⟨LinearEquiv.prodComm R E₁ E₂, by intro; simp [norm, sup_comm]⟩

/- TODO: in mathlib -/
@[simp]
theorem LinearIsometryEquiv.coe_prodComm
    (R : Type*) [Semiring R]
    (E₁ : Type*) [SeminormedAddCommGroup E₁] [Module R E₁]
    (E₂ : Type*) [SeminormedAddCommGroup E₂] [Module R E₂] :
    (LinearIsometryEquiv.prodComm R E₁ E₂ : E₁ × E₂ → E₂ × E₁) = Equiv.prodComm E₁ E₂ :=
  rfl

/- TODO: in mathlib -/
@[simp]
theorem LinearIsometryEquiv.coe_prodComm_symm
    (R : Type*) [Semiring R]
    (E₁ : Type*) [SeminormedAddCommGroup E₁] [Module R E₁]
    (E₂ : Type*) [SeminormedAddCommGroup E₂] [Module R E₂] :
    ((LinearIsometryEquiv.prodComm R E₁ E₂).symm : E₂ × E₁ → E₁ × E₂) =
    (Equiv.prodComm E₁ E₂).symm :=
  rfl

/- TODO: in mathlib -/
@[simp]
theorem LinearIsometryEquiv.prodComm_symm
    (R : Type*) [Semiring R]
    (E₁ : Type*) [SeminormedAddCommGroup E₁] [Module R E₁]
    (E₂ : Type*) [SeminormedAddCommGroup E₂] [Module R E₂] :
    (LinearIsometryEquiv.prodComm R E₁ E₂).symm = LinearIsometryEquiv.prodComm R E₂ E₁ :=
  rfl

/- TODO: in mathlib -/
@[simp]
theorem Finset.sup_univ_surj
    {α : Type*} [Fintype α] {β : Type*} [Fintype β] {f : α → β} (hf : Function.Surjective f)
    {γ : Type*} [SemilatticeSup γ] [OrderBot γ] (g : β → γ) :
    univ.sup (g ∘ f) = univ.sup g := by
  apply le_antisymm
  · simp; intro; apply le_sup; exact mem_univ _
  · simp; intro x; rcases hf x with ⟨a, rfl⟩
    rw [← @Function.comp_apply _ _ _ g]
    exact le_sup (mem_univ _)

/- TODO: in mathlib? PiLp.equivₗᵢ -/
def LinearIsometryEquiv.piCongrLeft
    (𝕜 : Type*) [Semiring 𝕜] {ι : Type*} [Fintype ι] {ι' : Type*} [Fintype ι']
    (E : Type*) [SemilatticeSup E] [SeminormedAddCommGroup E] [Module 𝕜 E]
    (e : ι ≃ ι') :
    (ι → E) ≃ₗᵢ[𝕜] (ι' → E) where
  toLinearEquiv := LinearEquiv.piCongrLeft' 𝕜 (fun _ ↦ E) e
  norm_map' x := by
    simp [LinearEquiv.piCongrLeft', Equiv.piCongrLeft', norm]
    exact Finset.sup_univ_surj e.symm.surjective fun b ↦ ‖x b‖₊

theorem piCongrLeft_linearIsometryEquiv_measurableEquiv_coe
    (𝕜 : Type*) [Semiring 𝕜] {ι : Type*} [Fintype ι] {ι' : Type*} [Fintype ι']
    (E : Type*) [SemilatticeSup E] [SeminormedAddCommGroup E] [Module 𝕜 E] [MeasurableSpace E]
    (e : ι ≃ ι') :
    (LinearIsometryEquiv.piCongrLeft 𝕜 E e : (ι → E) → ι' → E) =
    (MeasurableEquiv.piCongrLeft (fun _ ↦ E) e : (ι → E) → ι' → E) := by
  simp [LinearIsometryEquiv.piCongrLeft, MeasurableEquiv.piCongrLeft, LinearEquiv.piCongrLeft',
    Equiv.piCongrLeft]

theorem LinearIsometryEquiv.coe_piCongrLeft
    (𝕜 : Type*) [Semiring 𝕜] {ι : Type*} [Fintype ι] {ι' : Type*} [Fintype ι']
    (E : Type*) [SemilatticeSup E] [SeminormedAddCommGroup E] [Module 𝕜 E]
    (e : ι ≃ ι') :
    (LinearIsometryEquiv.piCongrLeft 𝕜 E e : (ι → E) → ι' → E) =
    Equiv.piCongrLeft (fun _ ↦ E) e := by
  simp [LinearIsometryEquiv.piCongrLeft, LinearEquiv.piCongrLeft', Equiv.piCongrLeft]

theorem helper_lemma₉
    {f : (ι → ℝ) → ℝ} {n m : ℕ} (h₁ : Integrable f volume)
    (h₂ : ι ≃ ULift.{u} (Fin n) ⊕ ULift.{u} (Fin m)) :
    Integrable
      (f ∘ ⇑(MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) h₂.symm) ∘
        ⇑(MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ).symm)
      (volume.prod volume) := by
  rw [← Function.comp_assoc]
  apply Integrable.comp_measurable _
    (MeasurableEquiv.measurable (MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ).symm)
  apply Integrable.comp_measurable _
    (MeasurableEquiv.measurable (MeasurableEquiv.piCongrLeft (fun x ↦ ℝ) h₂.symm))
  have := (measurePreserving_sumPiEquivProdPi fun _ : ULift.{u} (Fin n) ⊕ ULift.{u} (Fin m) ↦
    (volume : Measure ℝ)).symm
  have := this.map_eq
  simp_rw [← volume_pi] at this; rw [this]
  rw [(volume_measurePreserving_piCongrLeft (fun _ : ι ↦ ℝ) h₂.symm).map_eq]
  exact h₁

theorem helper_lemma₁₀
    {f : (ι → ℝ) → ℝ} {n m : ℕ} (h₁ : Integrable f volume)
    (h₂ :ι ≃ ULift.{u, 0} (Fin n) ⊕ ULift.{u, 0} (Fin m)) :
    Integrable
      (f ∘ ⇑(MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) h₂.symm) ∘
        ⇑(MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ).symm ∘ Prod.swap)
      (volume.prod volume) := by
  simp_rw [← Function.comp_assoc f, ← Function.comp_assoc]
  apply Integrable.swap
  exact helper_lemma₉ h₁ h₂

theorem helper_lemma₁₁ (f : ((EuclideanSpace ℝ ι) × (EuclideanSpace ℝ κ)) → ℝ) :
    Integrable f (volume : Measure ((EuclideanSpace ℝ ι) × (EuclideanSpace ℝ κ))) ↔
    Integrable f (volume : Measure ((ι → ℝ) × (κ → ℝ))) := by
  -- simp_rw [Measure.volume_eq_prod]
  have := MeasurePreserving.prod
    (EuclideanSpace.volume_preserving_measurableEquiv ι)
    (EuclideanSpace.volume_preserving_measurableEquiv κ)
  simp_rw [← Measure.volume_eq_prod] at this
  rw [← MeasurePreserving.integrable_comp_emb this]; rfl
  exact Measurable.measurableEmbedding (fun ⦃_⦄ ↦ id) fun ⦃_ _⦄ ↦ id

/- TODO: in mathlib? -/
theorem helper_lemma₁₂ {α : Type*} [Mul α] (a : α) {β : Type*} (f : β → α) :
    (fun b ↦ a * f b) = (Function.const β a) * f :=
  rfl

universe u in
theorem helper_lemma₁₃
    {ι : Type u} [Fintype ι] {κ₁ : Type u} [Fintype κ₁] {κ₂ : Type u} [Fintype κ₂]
    (h : ι ≃ κ₁ ⊕ κ₂) {f : EuclideanSpace ℝ ι → ℝ} (hf : Measurable f) :
    Measurable fun x ↦ ∫ (y : κ₂ → ℝ), f
      ((MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) h).symm
        ((MeasurableEquiv.sumPiEquivProdPi _).symm (x, y))) := by
  refine stronglyMeasurable_iff_measurable.mp (StronglyMeasurable.integral_prod_right
    (stronglyMeasurable_iff_measurable.mpr ?_))
  unfold Function.uncurry; simp only [Prod.mk.eta]
  simp_rw [← @Function.comp_apply _ _ _ f, ← @Function.comp_apply _ _ _ (f ∘ _)]
  exact (MeasurableEquiv.measurable_comp_iff (MeasurableEquiv.sumPiEquivProdPi fun a ↦ ℝ).symm).mpr
    ((MeasurableEquiv.measurable_comp_iff (MeasurableEquiv.piCongrLeft (fun x ↦ ℝ) h).symm).mpr hf)

omit [Fintype ι] in
theorem helper_lemma₁₄
    {f : (ι → ℝ) → ℝ} {n m : ℕ} (h₁ : Measurable f)
    (h₂ : ι ≃ ULift.{u} (Fin n) ⊕ ULift.{u} (Fin m)) :
    Measurable
      (f ∘ ⇑(MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) h₂.symm) ∘
        ⇑(MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ).symm) := by
  simp_rw [← Function.comp_assoc, MeasurableEquiv.measurable_comp_iff, h₁]

omit [Fintype ι] in
theorem helper_lemma₁₅ {α : Type*} [MeasurableSpace α] (f : EuclideanSpace ℝ ι → α) :
    Measurable f ↔ (@Measurable (ι → ℝ) α _ _ f) := by
  rfl

omit [Fintype ι] in
theorem helper_lemma₁₆
    {κ₁ : Type*} [Fintype κ₁] {κ₂ : Type*} [Fintype κ₂] (e : ι ≃ κ₁ ⊕ κ₂)
    {f : (ι → ℝ) → ENNReal} (hf : Measurable f) :
    AEMeasurable (fun y ↦ f ((MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) e.symm)
      ((MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ).symm y))) (volume.prod volume) := by
  apply hf.aemeasurable.comp_measurable
  apply (MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) e.symm).measurable.comp
  exact (MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ).symm.measurable

omit [Fintype ι] in
theorem helper_lemma₁₇
    {n m : ℕ} (e : ι ≃ ULift.{u, 0} (Fin n) ⊕ ULift.{u, 0} (Fin m))
    {f : (ι → ℝ) → ENNReal} (hf : Measurable f) :
    Measurable fun y : ULift.{u} (Fin m) → ℝ ↦ ∫⁻ (x : ULift.{u} (Fin n) → ℝ),
      f ((MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) e.symm)
        ((MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ).symm (x, y))) := by
  apply Measurable.lintegral_prod_left
  apply hf.comp; simp_rw [Prod.mk.eta]
  apply (MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) e.symm).measurable.comp
  exact (MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ).symm.measurable

omit [Fintype ι] in
theorem helper_lemma₁₈
    {n m : ℕ} (e : ι ≃ ULift.{u, 0} (Fin n) ⊕ ULift.{u, 0} (Fin m))
    {f : (ι → ℝ) → ENNReal} (hf : Measurable f) (y : ULift.{u, 0} (Fin m) → ℝ) :
    Measurable fun x ↦ f ((MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) e.symm)
      ((MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ).symm (x, y))) := by
  apply hf.comp
  apply (MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) e.symm).measurable.comp
  apply (MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ).symm.measurable.comp
  exact measurable_prodMk_right

omit [Fintype ι] in
theorem helper_lemma₁₈'
    {n m : ℕ} (e : ι ≃ ULift.{u, 0} (Fin n) ⊕ ULift.{u, 0} (Fin m)) (y : ULift.{u, 0} (Fin m) → ℝ) :
    Measurable fun x ↦ (MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) e.symm)
      ((MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ).symm (x, y)) := by
  apply (MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) e.symm).measurable.comp
  apply (MeasurableEquiv.sumPiEquivProdPi fun x ↦ ℝ).symm.measurable.comp
  exact measurable_prodMk_right

theorem helper_lemma₁₉ (ι : Type*) [Fintype ι] (κ : Type*) [Fintype κ]:
    Measure.QuasiMeasurePreserving (MeasurableEquiv.sumPiEquivProdPi fun (_ : ι ⊕ κ) ↦ ℝ) :=
  ⟨(MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ).measurable,
    Measure.absolutelyContinuous_of_eq (volume_measurePreserving_sumPiEquivProdPi fun _ ↦ ℝ).map_eq⟩

/- Note: `Measurable f` for `f : (ι → ℝ) → ENNReal` implies `StronglyMeasurable f`. -/
set_option maxHeartbeats 0 in
universe u in
theorem prekopa_leindler''
    {ι : Type u} [Fintype ι]
    {t : ℝ} (ht₁ : 0 < t) (ht₂ : t < 1)
    {f : (ι → ℝ) → ENNReal} (hf₁ : Measurable f)
    {g : (ι → ℝ) → ENNReal} (hg₁ : Measurable g)
    {h : (ι → ℝ) → ENNReal} (hh₁ : Measurable h)
    (h₀ : ∀ᵐ (x) (y), (f x) ^ (1 - t) * (g y) ^ t ≤ h (x + y)) :
    (∫⁻ x, f x) ^ (1 - t) * (∫⁻ y, g y) ^ t ≤
    (ENNReal.ofReal (1 - t)) ^ ((1 - t) * Fintype.card ι) *
    (ENNReal.ofReal t) ^ (t * Fintype.card ι) * (∫⁻ z, h z) := by
  induction h₁ : Fintype.card ι using Nat.induction_on_add generalizing ι
  case hzero =>
    rw [Fintype.card_eq_zero_iff] at h₁; simp_rw [ae_iff_of_countable] at h₀; simp [Unique.uniq]
    have : {(0 : ι → ℝ)} = Set.univ := by ext; simp [Unique.uniq]
    simp [this] at h₀; apply le_trans (h₀ _ _) (le_of_eq _); congr; simp only [Unique.uniq]
  case hone =>
    sorry
  case hadd n hn m hm i =>
    let e := helper_def₁ ((h₁ ▸ Fintype.equivFin ι).trans finSumFinEquiv.symm)
    simp_rw [← helper_lemma₃' e.symm, helper_lemma₄', Measure.volume_eq_prod] at h₀ ⊢
    rw [lintegral_prod_symm, lintegral_prod_symm, lintegral_prod_symm]
    any_goals exact helper_lemma₁₆ _ (by assumption)
    simp_rw [Nat.cast_add, mul_add]
    rw [ENNReal.rpow_add (t * _) (t * _) (by simp [ht₁]) (by simp),
      ENNReal.rpow_add ((1 - t) * _) ((1 - t) * _) (by simp [ht₂]) (by simp),
      mul_comm ((ENNReal.ofReal t) ^ _), ← mul_assoc (_ * _),
      mul_assoc ((ENNReal.ofReal (1 - t)) ^ _), mul_comm ((ENNReal.ofReal (1 - t)) ^ _) (_ * _),
      mul_assoc (((ENNReal.ofReal (1 - t)) ^ _) * _),
      mul_assoc _ (((ENNReal.ofReal (1 - t)) ^ _) * _),
      ← MeasureTheory.lintegral_const_mul]
    any_goals exact (Measurable.lintegral_prod_right (hh₁.comp
      ((MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) e.symm).measurable.comp
        ((MeasurableEquiv.measurable (MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ).symm).comp
          (measurable_swap_iff.mp fun ⦃_⦄ ↦ id)))))
    refine hm ?_ ?_ ?_ ?_ (Fintype.card_ulift.{0, u} (Fin m) ▸ (Fintype.card_fin m))
    any_goals apply Measurable.const_mul
    any_goals exact helper_lemma₁₇ e (by assumption)
    -- filter_upwards with y₁; filter_upwards with y₂
    -- refine hn ?_ ?_ ?_ ?_ (Fintype.card_ulift.{0, u} (Fin n) ▸ (Fintype.card_fin n))
    -- any_goals exact helper_lemma₁₈ e (by assumption) _
    -- have h₂ (x₁ x₂ : ULift.{u} (Fin n) → ℝ) :
    --     (MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) e.symm)
    --       ((MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ).symm (x₁ + x₂, y₁ + y₂)) =
    --     (MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) e.symm)
    --       ((MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ).symm (x₁, y₁)) +
    --     (MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) e.symm)
    --       ((MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ).symm (x₂, y₂)) := by
    --   simp_rw [MeasurableEquiv.coe_piCongrLeft, ← LinearIsometryEquiv.coe_piCongrLeft ℝ,
    --     ← LinearIsometryEquiv.map_add]; congr
    --   simp_rw [MeasurableEquiv.coe_sumPiEquivProdPi_symm]
    --   exact (Equiv.sumPiEquivProdPi fun _ ↦ ℝ).symm_apply_eq.mpr rfl
    -- simp_rw [h₂]
    -- -- apply helper_lemma₁₉ h₀
    -- sorry
    -- -- simp_rw [h₂]; simp_rw [Filter.eventually_iff_exists_mem] at h₀ ⊢
    -- -- rcases h₀ with ⟨s₁, hs₁, hs₂⟩
    -- -- let f₁ x y (s : Set (ι → ℝ)) := (MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) e.symm)
    -- --   ((MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ).symm (x, y)) ∈ s
    -- -- use fun x ↦ f₁ x y₁ s₁; constructor
    -- -- · sorry
    -- -- intro x₁ hx₁; rcases hs₂ _ hx₁ with ⟨s₂, hs₂, hs₃⟩
    -- -- use fun x ↦ f₁ x y₂ s₂; constructor
    -- -- · sorry
    -- -- intro x₂ hx₂; exact hs₃ _ hx₂
    sorry

theorem prekopa_leindler'
    {ι : Type*} [Fintype ι]
    {t : ℝ} (ht₁ : 0 < t) (ht₂ : t < 1)
    {f : EuclideanSpace ℝ ι → ℝ} (hf₁ : HasFiniteIntegral f) (hf₂ : Measurable f) (hf₃ : 0 ≤ f)
    {g : EuclideanSpace ℝ ι → ℝ} (hg₁ : HasFiniteIntegral g) (hg₂ : Measurable g) (hg₃ : 0 ≤ g)
    {h : EuclideanSpace ℝ ι → ℝ} (hh₁ : HasFiniteIntegral h) (hh₂ : Measurable h)
    (h₀ : ∀ {x y}, (f x) ^ (1 - t) * (g y) ^ t ≤ h (x + y)) :
    (∫ x, f x) ^ (1 - t) * (∫ y, g y) ^ t ≤
    (1 - t) ^ ((1 - t) * Fintype.card ι) * t ^ (t * Fintype.card ι) * (∫ z, h z) := by
  have hf' : Measurable fun x ↦ENNReal.ofReal (f x) := Measurable.ennreal_ofReal hf₂
  have hg' : Measurable fun x ↦ENNReal.ofReal (g x) := Measurable.ennreal_ofReal hg₂
  have hh' : Measurable fun x ↦ENNReal.ofReal (h x) := Measurable.ennreal_ofReal hh₂
  have hh₃ : 0 ≤ h := by
    intro x; rw [Pi.zero_apply, ← zero_add x]
    refine le_trans (mul_nonneg_iff.mpr (.inl ?_)) h₀
    constructor <;> apply Real.rpow_nonneg <;> tauto
  have hpl := prekopa_leindler'' ht₁ ht₂
    (Measurable.ennreal_ofReal hf₂) (Measurable.ennreal_ofReal hg₂) (Measurable.ennreal_ofReal hh₂)
    (by
      filter_upwards with _; filter_upwards with _
      rw [← ENNReal.ofReal_rpow (hf₃ _) (by linarith), ← ENNReal.ofReal_rpow (hg₃ _) (by linarith),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (hf₃ _) (1 - t))]
      exact ENNReal.ofReal_le_ofReal h₀)
  repeat rw [integral_eq_lintegral_of_nonneg_ae]
  any_goals refine Filter.eventuallyLE_iff_all_subsets.mpr (fun x ↦ ?_)
  any_goals filter_upwards with _ _; tauto
  any_goals rw [aestronglyMeasurable_iff_aemeasurable]
  any_goals apply Measurable.aemeasurable (by assumption)
  simp_rw [ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
  rw [← ENNReal.toReal_ofReal_mul, ENNReal.toReal_le_toReal]
  any_goals (exact
    mul_nonneg_iff.mpr (.inl
      ⟨Real.rpow_nonneg (by linarith) _, Real.rpow_nonneg (by linarith) _⟩))
  any_goals apply ENNReal.mul_ne_top
  any_goals exact ENNReal.ofReal_ne_top
  any_goals apply ENNReal.rpow_ne_top_of_nonneg (by linarith)
  any_goals rw [← lt_top_iff_ne_top]
  any_goals refine Integrable.lintegral_lt_top ⟨?_, by assumption⟩
  any_goals rw [aestronglyMeasurable_iff_aemeasurable]
  any_goals apply Measurable.aemeasurable (by assumption)
  simp_rw [helper_lemma₁'']
  rw [ENNReal.ofReal_mul, ENNReal.ofReal_rpow, ENNReal.ofReal_rpow]; assumption
  any_goals linarith
  · positivity
  · exact mul_nonneg_iff.mpr (.inl ⟨by linarith, Nat.cast_nonneg _⟩)
  · exact Real.rpow_nonneg (by linarith) _

end
