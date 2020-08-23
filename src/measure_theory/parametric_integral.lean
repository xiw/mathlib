import measure_theory.interval_integral

open topological_space measure_theory filter first_countable_topology
open_locale topological_space filter

variables {α E : Type*} [measurable_space α] {μ : measure α}


variables [normed_group E] [second_countable_topology E] [normed_space ℝ E] [complete_space E]
  [measurable_space E] [borel_space E]

variables {X : Type*} [topological_space X] [first_countable_topology X]

lemma continuous_at_of_dominated {F : X → α → E} {x₀ : X} {bound : α → ℝ}
  (hF_meas : ∀ᶠ x in 𝓝 x₀, measurable (F x)) (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ a ∂μ, ∥F x a∥ ≤ bound a)
  (bound_integrable : integrable bound μ) (h_cont : ∀ᵐ a ∂μ, continuous_at (λ x, F x a) x₀) :
  continuous_at (λn, ∫ a, F n a ∂μ) x₀ :=
tendsto_integral_filter_of_dominated_convergence
  (first_countable_topology.nhds_generated_countable x₀) ‹_› (mem_of_nhds hF_meas) ‹_› ‹_› ‹_›

lemma continuous_of_dominated {F : X → α → E} {x₀ : X} {bound : α → ℝ}
  (hF_meas : ∀ x, measurable (F x)) (h_bound : ∀ x, ∀ᵐ a ∂μ, ∥F x a∥ ≤ bound a)
  (bound_integrable : integrable bound μ) (h_cont : ∀ᵐ a ∂μ, continuous (λ x, F x a)) :
  continuous (λn, ∫ a, F n a ∂μ) :=
continuous_iff_continuous_at.mpr (λ x₀, continuous_at_of_dominated (eventually_of_forall hF_meas)
  (eventually_of_forall h_bound) ‹_› $ h_cont.mono $ λ _, continuous.continuous_at)


lemma continuous_at_of_dominated {F : X → α → E} {x₀ : X} {bound : α → ℝ}
  (hF_meas : ∀ᶠ x in 𝓝 x₀, measurable (F x)) (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ a ∂μ, ∥F x a∥ ≤ bound a)
  (bound_integrable : integrable bound μ) (h_cont : ∀ᵐ a ∂μ, continuous_at (λ x, F x a) x₀) :
  continuous_at (λn, ∫ a, F n a ∂μ) x₀ :=
