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

noncomputable instance {α β : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    [SecondCountableTopologyEither α β] {p : ENNReal} [Fact (1 ≤ p)] :
    BorelSpace (WithLp p (α × β)) :=
  inferInstanceAs <| BorelSpace (α × β)

--instance : SFinite (volume : Measure (EuclideanSpace ℝ ι)) :=
--  sorry

omit [Fact (1 ≤ p)] in
theorem additional_lemma
    {α : Type*} {β : Type*} (f : WithLp p α → β) (a : α) :
    f (a : WithLp p α) = f a :=
  rfl

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
  let F (x₁ : EuclideanSpace ℝ ι) : EuclideanSpace ℝ κ → ℝ := fun x₂ ↦ f (eqvₗᵢ.symm (x₁, x₂))
  let G (y₁ : EuclideanSpace ℝ ι) : EuclideanSpace ℝ κ → ℝ := fun y₂ ↦ g (eqvₗᵢ.symm (y₁, y₂))
  let H (z₁ : EuclideanSpace ℝ ι) : EuclideanSpace ℝ κ → ℝ := fun z₂ ↦ h (eqvₗᵢ.symm (z₁, z₂))
  have hF₁ {x₁} : Integrable (F x₁) := by
    simp [F]; have := (integrable_comp eqvₗᵢ.symm f).mpr hf₁; exact?
    
  have hF₂ {x₁} (x₂) : 0 ≤ F x₁ x₂ := hf₂ _
  have hG₁ {x₁} : Integrable (G x₁) := sorry
  have hG₂ {y₁} (y₂) : 0 ≤ G y₁ y₂ := hg₂ _
  let m : MeasureTheory.MeasurePreserving eqvₗᵢ.symm.toMeasurableEquiv := sorry
  rw [← m.map_eq]
  have hf₃ := @MeasureTheory.integral_map_equiv _ _ _ _ _ volume _ _ eqvₗᵢ.symm.toMeasurableEquiv f
  have hg₃ := @MeasureTheory.integral_map_equiv _ _ _ _ _ volume _ _ eqvₗᵢ.symm.toMeasurableEquiv g
  have hh₃ := @MeasureTheory.integral_map_equiv _ _ _ _ _ volume _ _ eqvₗᵢ.symm.toMeasurableEquiv h
  rw [hf₃, hg₃, hh₃, LinearIsometryEquiv.coe_toMeasurableEquiv]
  have h₁ (f : WithLp 2 ((EuclideanSpace ℝ ι) × (EuclideanSpace ℝ κ)) → ℝ) :
      ∫ (x : WithLp 2 ((EuclideanSpace ℝ ι) × (EuclideanSpace ℝ κ))), f x ∂volume =
      ∫ (x : (EuclideanSpace ℝ ι) × (EuclideanSpace ℝ κ)), f x ∂volume.prod volume := by
    rw [Measure.volume_eq_prod]; rfl
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
end PrekopaLeindler

-- TODO: Add PrekopaLeindler.Statement
