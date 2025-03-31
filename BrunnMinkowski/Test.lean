import Mathlib

open MeasureTheory

noncomputable instance {α : Type*} [MeasurableSpace α] {p : ENNReal} [Fact (1 ≤ p)] :
    MeasurableSpace (WithLp p α) :=
  ‹MeasurableSpace α›

noncomputable instance {α β : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    [SecondCountableTopologyEither α β] {p : ENNReal} [Fact (1 ≤ p)] :
    BorelSpace (WithLp p (α × β)) :=
  inferInstanceAs <| BorelSpace (α × β)

lemma lemma_1
    {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]
    {f : EuclideanSpace ℝ (ι ⊕ κ) → ℝ} (hf : Integrable f) :
    let e :
        EuclideanSpace ℝ (ι ⊕ κ) ≃ₗᵢ[ℝ] WithLp 2 ((EuclideanSpace ℝ ι) × (EuclideanSpace ℝ κ)) :=
      PiLp.sumPiLpEquivProdLpPiLp _ _
    Integrable (f ∘ e.symm) :=
  (integrable_comp _ f).mpr hf

lemma lemma_2
    {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]
    {f : WithLp 2 ((EuclideanSpace ℝ ι) × (EuclideanSpace ℝ κ)) → ℝ}
    (hf : Integrable f) :
    ∫ (x : WithLp 2 ((EuclideanSpace ℝ ι) × (EuclideanSpace ℝ κ))), f x ∂volume =
    ∫ (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ), f x ∂volume := by
  sorry

-- Fubini's theorem on `WithLp` space
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
