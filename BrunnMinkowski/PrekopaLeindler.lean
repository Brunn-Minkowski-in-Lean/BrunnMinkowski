import Mathlib

namespace PrekopaLeindler

open MeasureTheory

variable {t : ℝ} (ht₁ : 0 < t) (ht₂ : t < 1)
variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]
variable {p : ENNReal} [Fact (1 ≤ p)]

section

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
variable {β : Type*} [TopologicalSpace β] [MeasurableSpace β]

--def MeasurableSpace.withLp_prod
--    (m₁ : MeasurableSpace α) (m₂ : MeasurableSpace β) :
--    MeasurableSpace (WithLp p (α × β)) :=
--  m₁.comap

noncomputable instance {α : Type*} [MeasurableSpace α] {p : ENNReal} [Fact (1 ≤ p)] :
    MeasurableSpace (WithLp p α) :=
  ‹MeasurableSpace α›

def measure_of_withLp2_measure {α : Type*} [MeasurableSpace α] {p : ENNReal} [Fact (1 ≤ p)] (μ: Measure (WithLp p α)):Measure α :=μ

noncomputable instance
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    {β : Type*} [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    [SecondCountableTopologyEither α β] {p : ENNReal} [Fact (1 ≤ p)] :
    BorelSpace (WithLp p (α × β)) :=
  inferInstanceAs <| BorelSpace (α × β)

noncomputable def EuclideanSpace.Prod.orthonormalBasis
    (ι : Type*) [Fintype ι] (κ : Type*) [Fintype κ] :
    OrthonormalBasis (ι ⊕ κ) ℝ (WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)) where
  repr := (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ ↦ ℝ)).symm

noncomputable def euclideanProd
    {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]
    (μ : Measure (EuclideanSpace ℝ ι)) (ν : Measure (EuclideanSpace ℝ κ)):
    Measure (WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)) :=
  μ.bind fun x ↦ ν.map (fun y ↦ ⟨x, y⟩)

noncomputable instance Prod.EuclideanSpace.measureSpace
    {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] :
    MeasureSpace (WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)) where
  volume := euclideanProd volume volume

theorem EuclideanSpace.volume_eq_prod_norm
    {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] :
    (volume : Measure (WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ))) =
    euclideanProd
      (volume : Measure (EuclideanSpace ℝ ι)) (volume : Measure (EuclideanSpace ℝ κ)) :=
  rfl

theorem Measurable.euclideanProdMk
    {α : Type*} [MeasurableSpace α] {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]
    {f : α → EuclideanSpace ℝ ι} {g : α → EuclideanSpace ℝ κ}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a : α ↦ ((f a, g a) : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)) :=
  Measurable.prod hf hg


theorem measurable_euclideanProdMk_left
    {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]
    {mι : MeasurableSpace (EuclideanSpace ℝ ι)} {mκ : MeasurableSpace (EuclideanSpace ℝ κ)} :
    Measurable fun x : EuclideanSpace ℝ ι ↦
      (fun y : EuclideanSpace ℝ κ ↦ ((x, y) : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ))) :=
  sorry

theorem euclideanProd_measure_eq_prod_measure {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]
    (μ : Measure (EuclideanSpace ℝ ι)) (ν : Measure (EuclideanSpace ℝ κ)):
    euclideanProd μ ν = μ.prod ν := by
  rw [euclideanProd]
  rw [MeasureTheory.Measure.prod]


theorem lintegral_euclideanProd_of_measurable
    {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]
    {μ : Measure (EuclideanSpace ℝ ι)} {ν : Measure (EuclideanSpace ℝ κ)} [SFinite ν]
    (f : (WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)) → ENNReal) :
    Measurable f → ∫⁻ z, f z ∂(euclideanProd μ ν) = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ := by
  rw [euclideanProd_measure_eq_prod_measure]
  intros mf
  simp [WithLp] at f
  simp [WithLp]
  rw [MeasureTheory.lintegral_prod_of_measurable]
  exact mf

theorem hasFiniteIntegral_euclideanProd_iff
    {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]
    {μ : Measure (EuclideanSpace ℝ ι)} {ν : Measure (EuclideanSpace ℝ κ)} [SFinite ν]
    ⦃f : (WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)) → ℝ⦄
    (h1f : StronglyMeasurable f) :
    HasFiniteIntegral f (euclideanProd μ ν) ↔
    (∀ᵐ x ∂μ, HasFiniteIntegral (fun y ↦ f (x, y)) ν) ∧
    HasFiniteIntegral (fun x ↦ ∫ y, ‖f (x, y)‖ ∂ν) μ := by
  rw [euclideanProd_measure_eq_prod_measure]
  rw [hasFiniteIntegral_prod_iff]
  exact h1f

theorem hasFiniteIntegral_euclideanProd_iff'
    {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]
    {μ : Measure (EuclideanSpace ℝ ι)} {ν : Measure (EuclideanSpace ℝ κ)} [SFinite ν]
    ⦃f : (WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)) → ℝ⦄
    (h1f : AEStronglyMeasurable f (euclideanProd μ ν)) :
    HasFiniteIntegral f (euclideanProd μ ν) ↔
    (∀ᵐ x ∂μ, HasFiniteIntegral (fun y ↦ f (x, y)) ν) ∧
    HasFiniteIntegral (fun x ↦ ∫ y, ‖f (x, y)‖ ∂ν) μ := by
  rw [euclideanProd_measure_eq_prod_measure]
  rw [hasFiniteIntegral_prod_iff']
  rw [Eq.symm (euclideanProd_measure_eq_prod_measure _ _)]
  exact h1f

theorem integrable_euclideanProd_iff
    {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]
    {μ : Measure (EuclideanSpace ℝ ι)} {ν : Measure (EuclideanSpace ℝ κ)} [SFinite ν]
    ⦃f : (WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)) → ℝ⦄
    (h1f : AEStronglyMeasurable f (euclideanProd μ ν)) :
    Integrable f (euclideanProd μ ν) ↔
    (∀ᵐ x ∂μ, Integrable (fun y ↦ f (x, y)) ν) ∧ Integrable (fun x ↦ ∫ y, ‖f (x, y)‖ ∂ν) μ := by
  rw [euclideanProd_measure_eq_prod_measure]
  rw [integrable_prod_iff]
  rw [Eq.symm (euclideanProd_measure_eq_prod_measure _ _)]
  exact h1f

theorem Integrable.integral_norm_euclideanProd_left
    {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]
    {μ : Measure (EuclideanSpace ℝ ι)} {ν : Measure (EuclideanSpace ℝ κ)} [SFinite ν]
    ⦃f : (WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)) → ℝ⦄
    (hf : Integrable f (euclideanProd μ ν)) :
    Integrable (fun x ↦ ∫ y, ‖f (x, y)‖ ∂ν) μ := by
  simp [WithLp] at f
  apply MeasureTheory.Integrable.integral_norm_prod_left
  rw [Eq.symm (euclideanProd_measure_eq_prod_measure _ _)]
  exact hf

theorem Integrable.integral_euclideanProd_left
    {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]
    {μ : Measure (EuclideanSpace ℝ ι)} {ν : Measure (EuclideanSpace ℝ κ)}
    ⦃f : (WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)) → ℝ⦄ [SFinite ν ]
    (hf : Integrable f (euclideanProd μ ν)) :
    Integrable (fun x ↦ ∫ y, f (x, y) ∂ν) μ := by
  simp [WithLp] at f
  apply MeasureTheory.Integrable.integral_prod_left
  rw [Eq.symm (euclideanProd_measure_eq_prod_measure _ _)]
  exact hf

theorem EuclideanSpace.continuous_integral_integral
    {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]
    {μ : Measure (EuclideanSpace ℝ ι)}
    {ν : Measure (EuclideanSpace ℝ κ)} [SFinite ν] :
    Continuous fun (f : Lp ℝ 1 (euclideanProd μ ν)) ↦
      ∫ (x : EuclideanSpace ℝ ι), ∫ (y : EuclideanSpace ℝ κ), f (x, y) ∂ν ∂μ := by
  rw [continuous_iff_continuousAt]; intro g
  apply tendsto_integral_of_L1 _
    (Integrable.integral_euclideanProd_left (L1.integrable_coeFn g))
    (Filter.Eventually.of_forall fun h ↦
      Integrable.integral_euclideanProd_left (L1.integrable_coeFn h))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _ (fun _ ↦ zero_le _)
  · sorry
  · sorry
  · sorry


theorem EuclideanSpace.integral_prod
    {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]
    {μ : Measure (EuclideanSpace ℝ ι)}
    {ν : Measure (EuclideanSpace ℝ κ)} [SFinite ν]
    (f : (WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)) → ℝ)
    (hf : Integrable f (euclideanProd μ ν)) :
    ∫ (z : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)), f z ∂(euclideanProd μ ν) =
    ∫ (x : EuclideanSpace ℝ ι), ∫ (y : EuclideanSpace ℝ κ), f (x, y) ∂ν ∂μ := by
  revert f; apply Integrable.induction
  · sorry
  · sorry
  · exact isClosed_eq continuous_integral EuclideanSpace.continuous_integral_integral
  · sorry

--open Measure in
--noncomputable def WithLp.prod
--    (p : ENNReal) [Fact (1 ≤ p)]
--    [MeasureSpace α] (μ : Measure α)
--    [MeasureSpace β] (ν : Measure β) :
--    Measure (WithLp p (α × β)) :=
--  bind μ fun x : α ↦ map (Prod.mk x) ν

--theorem WithLp.volume_eq_prod :
--    (volume : Measure (WithLp 2 ((WithLp 2 α) × (WithLp 2 β)))) =
--    WithLp.prod 2 (volume : Measure (WithLp 2 α)) (volume : Measure (WithLp 2 β)) :=
--  sorry

theorem WithLp.integral_prod
    {α : Type*} [MeasurableSpace α]
    {β : Type*} [MeasurableSpace β]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ENNReal} [Fact (1 ≤ p)]
    {μ : Measure (WithLp p α)} [SFinite μ]
    {ν : Measure (WithLp p β)} [SFinite ν]
    (f : WithLp p (WithLp p α × WithLp p β) → E) (hf : Integrable f (μ.prod ν)) :
    ∫ (z : WithLp p (WithLp p α × WithLp p β)), f z ∂μ.prod ν =
    ∫ (x : WithLp p α), ∫ (y : WithLp p β), f (x, y) ∂ν ∂μ :=
  MeasureTheory.integral_prod f hf

set_option maxHeartbeats 1000000000 in
theorem condition_of_oplus
    {t : ℝ} (ht₁ : 0 < t) (ht₂ : t < 1)
    {ι : Type*} [Fintype ι]
    (hι :
      {f : EuclideanSpace ℝ ι → ℝ} → Integrable f → (∀ x, 0 ≤ f x) →
      {g : EuclideanSpace ℝ ι → ℝ} → Integrable g → (∀ y, 0 ≤ g y) →
    {h : EuclideanSpace ℝ ι → ℝ} → Integrable h →
      (∀ x y, (f x) ^ (1 - t) * (g y) ^ t ≤ h (x + y)) →
      (∫ x, f x) ^ (1 - t) * (∫ y, g y) ^ t ≤
      (1 - t) ^ ((Fintype.card ι) * (1 - t)) * t ^ ((Fintype.card ι) * t) * (∫ z, h z))
    {κ : Type*} [Fintype κ]
    (hκ :
      {f : EuclideanSpace ℝ κ → ℝ} → Integrable f → (∀ x, 0 ≤ f x) →
      {g : EuclideanSpace ℝ κ → ℝ} → Integrable g → (∀ y, 0 ≤ g y) →
      {h : EuclideanSpace ℝ κ → ℝ} → Integrable h →
    (∀ x y, (f x) ^ (1 - t) * (g y) ^ t ≤ h (x + y)) →
      (∫ x, f x) ^ (1 - t) * (∫ y, g y) ^ t ≤
      (1 - t) ^ ((Fintype.card κ) * (1 - t)) * t ^ ((Fintype.card κ) * t) * (∫ z, h z))
    {f : EuclideanSpace ℝ (ι ⊕ κ) → ℝ} (hf₁ : Integrable f) (hf₂ : ∀ x, 0 ≤ f x)
    {g : EuclideanSpace ℝ (ι ⊕ κ) → ℝ} (hg₁ : Integrable g) (hg₂ : ∀ y, 0 ≤ g y)
    {h : EuclideanSpace ℝ (ι ⊕ κ) → ℝ} (hh₁ : Integrable h)
    (h₀ : ∀ x y, (f x) ^ (1 - t) * (g y) ^ t ≤ h (x + y)) :
    (∫ x, f x) ^ (1 - t) * (∫ y, g y) ^ t ≤
    (1 - t) ^ ((Fintype.card ι + Fintype.card κ) * (1 - t)) *
      t ^ ((Fintype.card ι + Fintype.card κ) * t) * (∫ z, h z) := by
  let eqvₗᵢ :
      EuclideanSpace ℝ (ι ⊕ κ) ≃ₗᵢ[ℝ] WithLp 2 ((EuclideanSpace ℝ ι) × (EuclideanSpace ℝ κ)) :=
    PiLp.sumPiLpEquivProdLpPiLp _ _
  let eqvₘ := LinearIsometryEquiv.toMeasurableEquiv eqvₗᵢ
  let F (x₁ : EuclideanSpace ℝ ι) : EuclideanSpace ℝ κ → ℝ := fun x₂ ↦ (f ∘ eqvₗᵢ.symm) (x₁, x₂)
  let G (y₁ : EuclideanSpace ℝ ι) : EuclideanSpace ℝ κ → ℝ := fun y₂ ↦ (g ∘ eqvₗᵢ.symm) (y₁, y₂)
  let H (z₁ : EuclideanSpace ℝ ι) : EuclideanSpace ℝ κ → ℝ := fun z₂ ↦ (h ∘ eqvₗᵢ.symm) (z₁, z₂)
  have hF₂ {x₁} (x₂) : 0 ≤ F x₁ x₂ := hf₂ _
  have hG₂ {y₁} (y₂) : 0 ≤ G y₁ y₂ := hg₂ _
  let m : MeasureTheory.MeasurePreserving eqvₗᵢ.symm.toMeasurableEquiv := sorry
  rw [← m.map_eq]
  have hf₃ := @MeasureTheory.integral_map_equiv _ _ _ _ _ volume _ _ eqvₗᵢ.symm.toMeasurableEquiv f
  have hg₃ := @MeasureTheory.integral_map_equiv _ _ _ _ _ volume _ _ eqvₗᵢ.symm.toMeasurableEquiv g
  have hh₃ := @MeasureTheory.integral_map_equiv _ _ _ _ _ volume _ _ eqvₗᵢ.symm.toMeasurableEquiv h
  rw [hf₃, hg₃, hh₃, LinearIsometryEquiv.coe_toMeasurableEquiv]
  have hhh (f : WithLp 2 ((EuclideanSpace ℝ ι) × (EuclideanSpace ℝ κ)) → ℝ) (hf : Integrable f) :
      ∫ (x : WithLp 2 ((EuclideanSpace ℝ ι) × (EuclideanSpace ℝ κ))), f x ∂volume =
      ∫ (x : WithLp 2 ((EuclideanSpace ℝ ι) × (EuclideanSpace ℝ κ))), f x ∂volume.prod volume := by
    rw [WithLp.integral_prod]
    · sorry
    · sorry
  have h₁ (f : WithLp 2 ((EuclideanSpace ℝ ι) × (EuclideanSpace ℝ κ)) → ℝ) :
      ∫ (x : WithLp 2 ((EuclideanSpace ℝ ι) × (EuclideanSpace ℝ κ))), f x ∂volume =
      ∫ (x : (EuclideanSpace ℝ ι) × (EuclideanSpace ℝ κ)), f x ∂volume.prod volume := by
    rw [← Measure.volume_eq_prod]
    sorry
  simp_rw [h₁]
  have h₂ {x₁ y₁} :
      (∫ x₂, F x₁ x₂) ^ (1 - t) * (∫ y₂, G y₁ y₂) ^ t ≤
      (1 - t) ^ ((Fintype.card κ) * (1 - t)) *
        t ^ ((Fintype.card κ) * t) * (∫ z₂, H (x₁ + y₁) z₂) := by
    apply hκ _ hF₂ _ hG₂
    · sorry
    · sorry
    · sorry
    · sorry
  sorry
  /-
  rw [integral_prod, integral_prod, integral_prod] <;> (try rw [integrable_prod_iff]) <;>
  (try apply And.intro)
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  -/

end

end PrekopaLeindler

-- TODO: Add PrekopaLeindler.Statement
