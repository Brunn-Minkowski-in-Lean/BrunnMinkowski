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

instance EuclideanSpace.instUnique {𝕜 ι : Type*} [Fintype ι] [IsEmpty ι] :
    Unique (EuclideanSpace 𝕜 ι) :=
  Pi.uniqueOfIsEmpty _

@[simp]
theorem EuclideanSpace.integral_of_empty_eq_one
    {ι : Type*} [Fintype ι] [IsEmpty ι] (f : EuclideanSpace ℝ ι → ℝ) :
    ∫ (x : EuclideanSpace ℝ ι), f x = f 0 := by
  simp [integral_unique, default, isEmptyElim]
  congr; funext; rw [PiLp.zero_apply]; tauto

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

theorem LinearIsometryEquiv.coe_toEquiv
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

set_option maxHeartbeats 0 in
universe u in
theorem prekopa_leindler''
    {ι : Type u} [Fintype ι]
    {t : ℝ} (ht₁ : 0 < t) (ht₂ : t < 1)
    {f : (ι → ℝ) → ℝ} (hf₁ : AEStronglyMeasurable f) (hf₂ : Measurable f) (hf₃ : 0 ≤ f)
    {g : (ι → ℝ) → ℝ} (hg₁ : AEStronglyMeasurable g) (hg₂ : Measurable g) (hg₃ : 0 ≤ g)
    {h : (ι → ℝ) → ℝ} (hh₁ : AEStronglyMeasurable h) (hh₂ : Measurable h) (hh₃ : 0 ≤ h)
    (h₀ : ∀ᵐ (x) (y), (f x) ^ (1 - t) * (g y) ^ t ≤ h (x + y)) :
    (∫⁻ x, ENNReal.ofReal (f x)) ^ (1 - t) * (∫⁻ y, ENNReal.ofReal (g y)) ^ t ≤
    (ENNReal.ofReal (1 - t)) ^ ((1 - t) * Fintype.card ι) *
    (ENNReal.ofReal t) ^ (t * Fintype.card ι) *
    (∫⁻ z, ENNReal.ofReal (h z)) := by
  induction h₁ : Fintype.card ι using Nat.induction_on_add generalizing ι
  case hzero =>
    rw [Fintype.card_eq_zero_iff] at h₁
    simp [h₁]
    simp_rw [ae_iff_of_countable] at h₀
    have : {(0 : ι → ℝ)} = Set.univ := by ext; simp [Unique.uniq]
    simp [Unique.uniq]
    rw [← ENNReal.ofReal_rpow (hf₃ _) (by linarith), ← ENNReal.ofReal_rpow (hg₃ _) (by linarith),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (hf₃ _) _), ENNReal.ofReal_le_ofReal_iff (hh₃ _)]
    simp [this] at h₀
    apply le_trans (h₀ _ _) (le_of_eq _)
    congr; simp only [Unique.uniq]
  case hone =>
    sorry
  case hadd n hn m hm i =>
    sorry

-- set_option maxHeartbeats 0 in
-- universe u in
-- theorem prekopa_leindler'
--     {ι : Type u} [Fintype ι]
--     {t : ℝ} (ht₁ : 0 < t) (ht₂ : t < 1)
--     {f : EuclideanSpace ℝ ι → ℝ} (hf₁ : Integrable f) (hf₂ : Measurable f) (hf₃ : 0 ≤ f)
--     {g : EuclideanSpace ℝ ι → ℝ} (hg₁ : Integrable g) (hg₂ : Measurable g) (hg₃ : 0 ≤ g)
--     {h : EuclideanSpace ℝ ι → ℝ} (hh₁ : Integrable h) (hh₂ : Measurable h)
--     (h₀ : ∀ {x y}, (f x) ^ (1 - t) * (g y) ^ t ≤ h (x + y)) :
--     (∫ x, f x) ^ (1 - t) * (∫ y, g y) ^ t ≤
--     (1 - t) ^ ((1 - t) * Fintype.card ι) * t ^ (t * Fintype.card ι) * (∫ z, h z) := by
--   induction h₁ : Fintype.card ι using Nat.induction_on_add generalizing ι
--   case hzero =>
--     rw [Fintype.card_eq_zero_iff] at h₁
--     simp [h₁]
--     nth_rw 3 [← add_zero 0]
--     exact h₀
--   case hone => sorry
--   case hadd n hn m hm i =>
--     simp_rw [helper_lemma₁ f, helper_lemma₁ g, helper_lemma₁ h]
--     rw [helper_lemma₂] at hf₁ hg₁ hh₁
--     simp only [EuclideanSpace, PiLp, WithLp] at f g h hn hm h₀
--     have h₂ := helper_def₁ ((h₁ ▸ Fintype.equivFin ι).trans finSumFinEquiv.symm)
--     rw [← Fintype.card_fin n, ← Fintype.card_fin m]
--     simp_rw [← helper_lemma₃ h₂.symm, helper_lemma₄, Measure.volume_eq_prod]
--     rw [integral_prod, integral_prod, integral_prod]
--     · let F : (ULift.{u} (Fin n) → ℝ) → ℝ := fun x ↦ ∫ (y : ULift.{u} (Fin m) → ℝ), f
--         ((MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) h₂).symm
--           ((MeasurableEquiv.sumPiEquivProdPi _).symm (x, y)))
--       have hF₁ : Integrable F := helper_lemma₇ h₂ hf₁
--       have hF₂ : Measurable F := helper_lemma₁₃ h₂ hf₂
--       have hF₃ : 0 ≤ F := helper_lemma₈ h₂ hf₃
--       let G : (ULift.{u} (Fin n) → ℝ) → ℝ := fun x ↦ ∫ (y : ULift.{u} (Fin m) → ℝ), g
--         ((MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) h₂).symm
--           ((MeasurableEquiv.sumPiEquivProdPi _).symm (x, y)))
--       have hG₁ : Integrable G := helper_lemma₇ h₂ hg₁
--       have hG₂ : Measurable G := helper_lemma₁₃ h₂ hg₂
--       have hG₃ : 0 ≤ G := helper_lemma₈ h₂ hg₃
--       let H : (ULift.{u} (Fin n) → ℝ) → ℝ := fun x ↦
--         (1 - t) ^ ((1 - t) * m) *
--         t ^ (t * m) *
--         ∫ (y : ULift.{u} (Fin m) → ℝ), h
--           ((MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) h₂).symm
--             ((MeasurableEquiv.sumPiEquivProdPi _).symm (x, y)))
--       have hH₁ : Integrable H := Integrable.const_mul (helper_lemma₇ h₂ hh₁) _
--       have hH₂ : Measurable H := Measurable.const_mul (helper_lemma₁₃ h₂ hh₂) _
--       have h₃ := hn ((helper_lemma₂ _).mpr hF₁) hF₂ hF₃ ((helper_lemma₂ _).mpr hG₁) hG₂ hG₃
--         ((helper_lemma₂ _).mpr hH₁) hH₂ ?_ (by simp)
--       · simp only [Prod.mk.eta, Fintype.card_fin, Nat.cast_add] at h₃ ⊢
--         have h₄ {x : ℝ} (hx : 0 < x) {n m : ℕ} : x ^ (x * (n + m)) = x ^ (x * n) * x ^ (x * m) := by
--           rw [mul_add x, Real.rpow_add hx]
--         rw [h₄ ht₁, h₄ (by linarith : 0 < 1 - t), mul_comm ((1 - t) ^ _), mul_comm (t ^ _),
--           ← mul_assoc, mul_assoc ((1 - t) ^ _), mul_comm ((1 - t) ^ _) (t ^ _), ← mul_assoc,
--           mul_assoc _ ((1 - t) ^ _) (t ^ _), mul_assoc (((1 - t) ^ _) * (t ^ _)),
--           ← integral_mul_left]
--         simp_rw [← integral_mul_left ((1 - t) ^ ((1 - t) * n) * t ^ (t * n))]
--         rw [← @integral_integral_swap _ _ _ _ _ _ _ _ _ _ _ (fun _ _ ↦ _ * _)]
--         rw [← @integral_integral_swap _ _ _ _ _ _ _ _ _ _ _ (fun _ _ ↦ f _),
--           ← @integral_integral_swap _ _ _ _ _ _ _ _ _ _ _ (fun _ _ ↦ g _)]
--         simp_rw [← helper_lemma₁]
--         · apply hm _ _ _ _ _ _ _ _ _ (by simp)
--           · simp_rw [← @Function.comp_apply _ _ _ (MeasurableEquiv.piCongrLeft _ _),
--               ← @Function.comp_apply _ _ _ f, ← Function.comp_assoc]
--             apply Integrable.integral_prod_right
--             rw [← Measure.volume_eq_prod, helper_lemma₁₁, Function.comp_assoc]
--             exact helper_lemma₉ hf₁ h₂
--           · rw [← stronglyMeasurable_iff_measurable]
--             apply StronglyMeasurable.integral_prod_right
--             rw [stronglyMeasurable_iff_measurable]
--             unfold Function.uncurry; simp only [Prod.mk.eta]
--             have {p : (ULift.{u, 0} (Fin m) → ℝ) × EuclideanSpace ℝ (ULift.{u, 0} (Fin n))} :
--                 (p.2, p.1) = p.swap :=
--               rfl
--             simp_rw [this, ← @Function.comp_apply _ _ _ f, ← @Function.comp_apply _ _ _ (f ∘ _),
--               ← @Function.comp_apply _ _ _ _ Prod.swap]
--             simp_rw [measurable_swap_iff]
--             exact helper_lemma₁₄ hf₂ h₂
--           · intro; apply integral_nonneg; intro; apply hf₃
--           · simp_rw [← @Function.comp_apply _ _ _ (MeasurableEquiv.piCongrLeft _ _),
--               ← @Function.comp_apply _ _ _ g, ← Function.comp_assoc]
--             apply Integrable.integral_prod_right
--             rw [← Measure.volume_eq_prod, helper_lemma₁₁, Function.comp_assoc]
--             exact helper_lemma₉ hg₁ h₂
--           · rw [← stronglyMeasurable_iff_measurable]
--             apply StronglyMeasurable.integral_prod_right
--             rw [stronglyMeasurable_iff_measurable]
--             unfold Function.uncurry; simp only [Prod.mk.eta]
--             have {p : (ULift.{u, 0} (Fin m) → ℝ) × EuclideanSpace ℝ (ULift.{u, 0} (Fin n))} :
--                 (p.2, p.1) = p.swap :=
--               rfl
--             simp_rw [this, ← @Function.comp_apply _ _ _ g, ← @Function.comp_apply _ _ _ (g ∘ _),
--               ← @Function.comp_apply _ _ _ _ Prod.swap]
--             simp_rw [measurable_swap_iff]
--             exact helper_lemma₁₄ hg₂ h₂
--           · intro; apply integral_nonneg; intro; apply hg₃
--           · simp_rw [integral_mul_left]; apply Integrable.const_mul'
--             simp_rw [← @Function.comp_apply _ _ _ (MeasurableEquiv.piCongrLeft _ _),
--               ← @Function.comp_apply _ _ _ h, ← Function.comp_assoc]
--             apply Integrable.integral_prod_right
--             rw [← Measure.volume_eq_prod, helper_lemma₁₁, Function.comp_assoc]
--             exact helper_lemma₉ hh₁ h₂
--           · simp_rw [integral_mul_left]; apply Measurable.const_mul
--             rw [← stronglyMeasurable_iff_measurable]
--             apply StronglyMeasurable.integral_prod_right
--             rw [stronglyMeasurable_iff_measurable]
--             unfold Function.uncurry; simp only [Prod.mk.eta]
--             have {p : (ULift.{u, 0} (Fin m) → ℝ) × EuclideanSpace ℝ (ULift.{u, 0} (Fin n))} :
--                 (p.2, p.1) = p.swap :=
--               rfl
--             simp_rw [this, ← @Function.comp_apply _ _ _ h, ← @Function.comp_apply _ _ _ (h ∘ _),
--               ← @Function.comp_apply _ _ _ _ Prod.swap]
--             simp_rw [measurable_swap_iff]
--             exact helper_lemma₁₄ hh₂ h₂
--           · intro x₁ y₁
--             rw [integral_mul_left]
--             apply hn _ _ _ _ _ _ _ _ _ (by simp)
--             · have {x : (ULift.{u, 0} (Fin n) → ℝ)} : (x, x₁) = (x₁, x).swap :=
--                 rfl
--               simp_rw [this]
--               sorry
--             · have {x : (ULift.{u, 0} (Fin n) → ℝ)} : (x, x₁) = (x₁, x).swap :=
--                 rfl
--               simp_rw [this]
--               exact Measurable.comp' hf₂ (Measurable.comp' (MeasurableEquiv.measurable _)
--                 (Measurable.comp' (MeasurableEquiv.measurable _) measurable_prodMk_right))
--             · sorry
--             · sorry
--             · have {y : (ULift.{u, 0} (Fin n) → ℝ)} : (y, y₁) = (y₁, y).swap :=
--                 rfl
--               simp_rw [this]
--               exact Measurable.comp' hg₂ (Measurable.comp' (MeasurableEquiv.measurable _)
--                 (Measurable.comp' (MeasurableEquiv.measurable _) measurable_prodMk_right))
--             · sorry
--             · sorry
--             · have {z : (ULift.{u, 0} (Fin n) → ℝ)} : (z, x₁ + y₁) = (x₁ + y₁, z).swap :=
--                 rfl
--               simp_rw [this]
--               exact Measurable.comp' hh₂ (Measurable.comp' (MeasurableEquiv.measurable _)
--                 (Measurable.comp' (MeasurableEquiv.measurable _) measurable_prodMk_right))
--             · intro x₂ y₂
--               have := @h₀
--                 ((MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) h₂.symm)
--                   ((MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ).symm (x₂, x₁)))
--                 ((MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) h₂.symm)
--                   ((MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ).symm (y₂, y₁)))
--               apply le_trans this (le_of_eq _); congr
--               simp_rw [MeasurableEquiv.coe_piCongrLeft, ← LinearIsometryEquiv.coe_toEquiv ℝ,
--                 ← LinearIsometryEquiv.map_add]; congr
--               simp_rw [MeasurableEquiv.coe_sumPiEquivProdPi_symm,
--                 ← LinearEquiv.sumPiEquivProdPi_symm_apply ℝ, ← LinearEquiv.map_add]
--               rfl
--         · simp_rw [← @Function.comp_apply _ _ _ g, ← @Function.comp_apply _ _ _ (g ∘ _)]
--           rw [uncurry_prod_swap]
--           exact helper_lemma₁₀ hg₁ h₂
--         · simp_rw [← @Function.comp_apply _ _ _ f, ← @Function.comp_apply _ _ _ (f ∘ _)]
--           rw [uncurry_prod_swap]
--           exact helper_lemma₁₀ hf₁ h₂
--         · simp_rw [← @Function.comp_apply _ _ _ h, ← @Function.comp_apply _ _ _ (h ∘ _),
--             ← @Function.comp_apply _ _ _ (((1 - t) ^ ((1 - t) * n) * (t ^ (t * n))) * ·)]
--           rw [uncurry_prod_swap]
--           exact Integrable.const_mul' (helper_lemma₁₀ hh₁ h₂) _

--       · intro x₁ y₁
--         simp [F, G, H]
--         sorry
--     all_goals (refine (integrable_prod_iff ?_).mpr ⟨?_, ?_⟩)
--     · let p₁ := (helper_lemma₆' h₂ h).mp hh₁;
--       let p₂ := (helper_lemma₅ _ ).mp p₁;
--       simp [Function.comp, Integrable] at p₂
--       exact (And.left p₂)

--     · let p₁ := (helper_lemma₆' h₂ h).mp hh₁;
--       let p₂ := (helper_lemma₅ _ ).mp p₁;
--       let p₃ := (MeasureTheory.Integrable.prod_right_ae p₂);
--       simp [Function.comp] at p₃
--       exact p₃

--     · let p₁ := (helper_lemma₆' h₂ h).mp hh₁;
--       let p₂ := (helper_lemma₅ _ ).mp p₁;
--       let p₃ := MeasureTheory.Integrable.norm p₂;
--       let p₄ := Integrable.integral_prod_left p₃;
--       simp [Function.comp] at p₄
--       exact p₄

--     · let p₁ := (helper_lemma₆' h₂ g).mp hg₁;
--       let p₂ := (helper_lemma₅ _ ).mp p₁;
--       simp [Function.comp, Integrable] at p₂
--       exact (And.left p₂)

--     · let p₁ := (helper_lemma₆' h₂ g).mp hg₁;
--       let p₂ := (helper_lemma₅ _ ).mp p₁;
--       let p₃ := (MeasureTheory.Integrable.prod_right_ae p₂);
--       simp [Function.comp] at p₃
--       exact p₃

--     · let p₁ := (helper_lemma₆' h₂ g).mp hg₁;
--       let p₂ := (helper_lemma₅ _ ).mp p₁;
--       let p₃ := MeasureTheory.Integrable.norm p₂;
--       let p₄ := Integrable.integral_prod_left p₃;
--       simp [Function.comp] at p₄
--       exact p₄

--     · let p₁ := (helper_lemma₆' h₂ f).mp hf₁;
--       let p₂ := (helper_lemma₅ _ ).mp p₁;
--       simp [Function.comp, Integrable] at p₂
--       exact (And.left p₂)

--     · let p₁ := (helper_lemma₆' h₂ f).mp hf₁;
--       let p₂ := (helper_lemma₅ _ ).mp p₁;
--       let p₃ := (MeasureTheory.Integrable.prod_right_ae p₂);
--       simp [Function.comp] at p₃
--       exact p₃

--     · let p₁ := (helper_lemma₆' h₂ f).mp hf₁;
--       let p₂ := (helper_lemma₅ _ ).mp p₁;
--       let p₃ := MeasureTheory.Integrable.norm p₂;
--       let p₄ := Integrable.integral_prod_left p₃;
--       simp [Function.comp] at p₄
--       exact p₄

end
