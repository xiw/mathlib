import measure_theory.interval_integral
import analysis.calculus.mean_value

open topological_space measure_theory filter first_countable_topology metric
open_locale topological_space filter nnreal


/-! # Ordered field -/
section ordered_field

lemma inv_mul_le_iff {α : Type*} [linear_ordered_field α] {a b c : α} (h : 0 < b) : b⁻¹*a ≤ c ↔ a ≤ b*c :=
begin
  rw [inv_eq_one_div, mul_comm, ← div_eq_mul_one_div],
  exact div_le_iff' h,
end

lemma inv_mul_le_iff' {α : Type*} [linear_ordered_field α] {a b c : α} (h : 0 < b) : b⁻¹*a ≤ c ↔ a ≤ c*b :=
by rw [inv_mul_le_iff h, mul_comm]

end ordered_field

/-! # Lipschitz -/

section lipschitz_on_with

open filter function
open_locale topological_space nnreal

variables {α  β: Type*}

/-- A function `f` is Lipschitz continuous with constant `K ≥ 0` on `s` if for all `x, y` in `s`
we have `dist (f x) (f y) ≤ K * dist x y` -/
def lipschitz_on_with [emetric_space α] [emetric_space β] (K : ℝ≥0) (s : set α) (f : α → β) :=
∀ x y ∈ s, edist (f x) (f y) ≤ K * edist x y

lemma lipschitz_on_with.mono [emetric_space α] [emetric_space β] {K : ℝ≥0} {s t : set α} {f : α → β}
  (hf : lipschitz_on_with K t f) (h : s ⊆ t) :lipschitz_on_with K s f :=
λ x y x_in y_in, hf _ _ (h x_in) (h y_in)

lemma lipschitz_on_with_iff_dist_le_mul [metric_space α] [metric_space β] {K : ℝ≥0} {s : set α} {f : α → β} :
  lipschitz_on_with K s f ↔ ∀ x y ∈ s, dist (f x) (f y) ≤ K * dist x y :=
by { simp only [lipschitz_on_with, edist_nndist, dist_nndist], norm_cast }

alias lipschitz_on_with_iff_dist_le_mul ↔ lipschitz_on_with.dist_le_mul lipschitz_on_with.of_dist_le_mul
end lipschitz_on_with


/-! # Filters -/

namespace filter

lemma is_countably_generated.inf {α : Type*} {f g : filter α} (hf : is_countably_generated f)
(hg : is_countably_generated g) : is_countably_generated (f ⊓ g) :=
begin
  rw is_countably_generated_iff_exists_antimono_basis at hf hg,
  rcases hf with ⟨s, hs⟩,
  rcases hg with ⟨t, ht⟩,
  exact has_countable_basis.is_countably_generated
    ⟨hs.to_has_basis.inf ht.to_has_basis, set.countable_encodable _⟩
end

lemma is_countably_generated_principal {α : Type*} (s : set α) : is_countably_generated (𝓟 s) :=
begin
  rw show 𝓟 s = ⨅ i : ℕ, 𝓟 s, by simp,
  apply is_countably_generated_seq
end

lemma is_countably_generated.inf_principal {α : Type*} {f : filter α} (h : is_countably_generated f)
  (s : set α) : is_countably_generated (f ⊓ 𝓟 s) :=
h.inf (filter.is_countably_generated_principal s)

lemma diff_mem_inf_principal_compl {α : Type*} {f : filter α} {s : set α} (hs : s ∈ f) (t : set α) :
  s \ t ∈ f ⊓ 𝓟 tᶜ :=
begin
  rw mem_inf_principal,
  filter_upwards [hs],
  intros a has hat,
  exact ⟨has, hat⟩
end

end filter

open filter

/-! # nnreal -/

@[simp] lemma nnreal.abs_eq (x : ℝ≥0) : abs (x : ℝ) = x :=
abs_of_nonneg x.property

@[simp] lemma nnreal.norm_eq (x : ℝ≥0) : ∥(x : ℝ)∥ = x :=
by rw [real.norm_eq_abs, x.abs_eq]

noncomputable def nnreal.abs : ℝ → ℝ≥0 := λ x, ⟨abs x, abs_nonneg x⟩

@[simp] lemma nnreal.coe_abs (x : ℝ) : (nnreal.abs x : ℝ) = abs x :=
by simp [nnreal.abs]

/-! # nhds_within -/

lemma diff_mem_nhds_within_compl {X : Type*} [topological_space X] {x : X} {s : set X}
  (hs : s ∈ 𝓝 x) (t : set X) : s \ t ∈ 𝓝[tᶜ] x :=
filter.diff_mem_inf_principal_compl hs t


/-! # First countable -/

section first_countable

lemma is_countably_generated_nhds {X : Type*} [topological_space X] [first_countable_topology X] (x : X) :
  is_countably_generated (𝓝 x) :=
first_countable_topology.nhds_generated_countable x

lemma is_countably_generated_nhds_within {X : Type*} [topological_space X] [first_countable_topology X] (x : X) (s : set X) :
  is_countably_generated (𝓝[s] x) :=
(first_countable_topology.nhds_generated_countable x).inf_principal s

end first_countable


/-! # const_mul -/

variables {α : Type*} [measurable_space α] {μ : measure α}

-- borel_space.lean, next to measurable.const_smul
lemma measurable.const_mul {f : α → ℝ} (h : measurable f) (c : ℝ) : measurable (λ x, c*f x) :=
(measurable.const_smul h c : _)

-- l1_space.lean, next to integrable.smul
lemma integrable.const_mul {f : α → ℝ} (h : integrable f μ) (c : ℝ) : integrable (λ x, c*f x) μ :=
(integrable.smul c h : _)

/-! # Integral with parameters -/

section

variables {E : Type*} [normed_group E] [second_countable_topology E] [normed_space ℝ E]
  [complete_space E] [measurable_space E] [borel_space E]

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

lemma integrable_of_norm_sub_le {f₀ f₁ : α → E} {g : α → ℝ}
  (hf₀_m : measurable f₀)
  (hf₀_i : integrable f₀ μ)
  (hg_m : measurable g)
  (hg_i : integrable g μ)
  (h : ∀ᵐ a ∂μ, ∥f₁ a - f₀ a∥ ≤ g a) :
  integrable f₁ μ :=
begin
  have : ∀ᵐ a ∂μ, ∥f₁ a∥ ≤ g a + ∥f₀ a∥,
  { apply h.mono,
    intros a ha,
    calc ∥f₁ a∥ = ∥f₁ a - f₀ a + f₀ a∥ : by simp
    ... ≤ ∥f₁ a - f₀ a∥ + ∥f₀ a∥ : norm_add_le _ _
    ... ≤ g a + ∥f₀ a∥ : add_le_add_right ha _  },
  exact integrable.mono' (hg_i.add hg_m hf₀_m.norm hf₀_i.norm) this,
end

lemma has_deriv_at_of_dominated_loc_of_lip' {F : ℝ → α → E} {F' : α → E} {x₀ : ℝ} {bound : α → ℝ}
  {ε : ℝ} (ε_pos : 0 < ε)
  (hF_meas : ∀ x ∈ ball x₀ ε, measurable (F x))
  (hF_int : integrable (F x₀) μ)
  (hF'_meas : measurable F')
  (h_lipsch : ∀ᵐ a ∂μ, lipschitz_on_with (nnreal.abs $ bound a) (ball x₀ ε) (λ x, F x a))
  (bound_measurable : measurable (bound : α → ℝ))
  (bound_integrable : integrable (bound : α → ℝ) μ)
  (h_diff : ∀ᵐ a ∂μ, has_deriv_at (λ x, F x a) (F' a) x₀) :
  has_deriv_at (λ x, ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀ :=
begin
  have x₀_in : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos,
  have hF_int' : ∀ x ∈ ball x₀ ε, integrable (F x) μ,
  { intros x x_in,
    have : ∀ᵐ a ∂μ, ∥F x a - F x₀ a∥ ≤ ε * ∥(bound a : ℝ)∥,
    { apply h_lipsch.mono,
      intros a ha,
      rw ← dist_eq_norm,
      apply (lipschitz_on_with_iff_dist_le_mul.mp ha x x₀ x_in x₀_in).trans,
      rw [mul_comm, nnreal.coe_abs, real.norm_eq_abs],
      rw mem_ball at x_in,
      apply mul_le_mul_of_nonneg_right (le_of_lt x_in) (abs_nonneg  _) },
    apply integrable_of_norm_sub_le (hF_meas x₀ x₀_in) hF_int _ _ this,
    exact measurable.const_mul (measurable_norm.comp bound_measurable) ε,
    apply integrable.const_mul bound_integrable.norm },
  have h_ball' : ((ball x₀ ε) \ {x₀})  ∈ 𝓝[{x₀}ᶜ] x₀ :=
    diff_mem_nhds_within_compl (ball_mem_nhds x₀ ε_pos) _,
  have h_ball: ball x₀ ε ∈ 𝓝[{x₀}ᶜ] x₀ :=
    mem_sets_of_superset h_ball' (set.diff_subset _ _),
  have : ∀ᶠ x in 𝓝[{x₀}ᶜ] x₀, (x - x₀)⁻¹ • (∫ a, F x a ∂μ - ∫ a, F x₀ a ∂μ) = ∫ a, (x - x₀)⁻¹ • (F x a - F x₀ a) ∂μ,
  { apply mem_sets_of_superset h_ball,
    intros x x_in,
    dsimp,
    rw [integral_smul, integral_sub (hF_meas x x_in) (hF_int' x x_in) (hF_meas _ x₀_in) hF_int] },
  rw [has_deriv_at_iff_tendsto_slope, tendsto_congr' this], clear this,
  apply tendsto_integral_filter_of_dominated_convergence,
  { apply is_countably_generated_nhds_within },
  { filter_upwards [h_ball],
    intros x x_in,
    apply measurable.const_smul,
    exact (hF_meas _ x_in).sub (hF_meas _ x₀_in), },
  { exact hF'_meas },
  { apply mem_sets_of_superset h_ball',
    intros x hx,
    have abs_ne : 0 < abs (x - x₀),
    { simp only [abs_pos_iff, ne.def, sub_eq_zero_iff_eq],
      rintro rfl,
      simpa using hx },
    apply (h_diff.and h_lipsch).mono,
    rintros a ⟨ha_deriv, ha_bound⟩,
    rw lipschitz_on_with_iff_dist_le_mul at ha_bound,
    rw [norm_smul, real.norm_eq_abs, abs_inv, inv_mul_le_iff' abs_ne, ← real.norm_eq_abs],
    simpa [dist_eq_norm] using ha_bound x x₀ hx.1 x₀_in },
  { rwa ← integrable_norm_iff at bound_integrable },
  { apply h_diff.mono,
    intros a ha,
    exact has_deriv_at_iff_tendsto_slope.mp ha }
end

lemma has_deriv_at_of_dominated_loc_of_lip {F : ℝ → α → E} {F' : α → E} {x₀ : ℝ} {bound : α → ℝ} {ε : ℝ}
  (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠ x in 𝓝 x₀, measurable (F x))
  (hF_int : integrable (F x₀) μ)
  (hF'_meas : measurable F')
  (h_lip : ∀ᵐ a ∂μ, lipschitz_on_with (nnreal.abs $ bound a) (ball x₀ ε) (λ x, F x a))
  (bound_measurable : measurable bound)
  (bound_integrable : integrable bound μ)
  (h_diff : ∀ᵐ a ∂μ, has_deriv_at (λ x, F x a) (F' a) x₀) :
  has_deriv_at (λ x, ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀ :=
begin
  obtain ⟨ε', ε'_pos, h'⟩ : ∃ ε' > 0, ∀ x ∈ ball x₀ ε', measurable (F x),
  by simpa using nhds_basis_ball.eventually_iff.mp hF_meas,
  set δ := min ε ε',
  have δ_pos : 0 < δ := lt_min ε_pos ε'_pos,
  replace h' : ∀ (x : ℝ), x ∈ ball x₀ δ → measurable (F x),
  { intros x x_in,
    exact h' _ (ball_subset_ball (min_le_right ε ε') x_in) },
  replace h_lip : ∀ᵐ (a : α) ∂μ, lipschitz_on_with (nnreal.abs $ bound a) (ball x₀ δ) (λ (x : ℝ), F x a),
  { apply h_lip.mono,
    intros a lip,
    exact lip.mono (ball_subset_ball $ min_le_left ε ε') },
  apply has_deriv_at_of_dominated_loc_of_lip' δ_pos  ; assumption
end

lemma has_deriv_at_of_dominated_loc_of_deriv_le {F : ℝ → α → E} {F' : ℝ → α → E} {x₀ : ℝ} {bound : α → ℝ} {ε : ℝ}
  (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠ x in 𝓝 x₀, measurable (F x))
  (hF_int : integrable (F x₀) μ)
  (hF'_meas : ∀ x ∈ ball x₀ ε, measurable (F' x))
  (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, ∥F' x a∥ ≤ bound a)
  (bound_measurable : measurable (bound : α → ℝ))
  (bound_integrable : integrable bound μ)
  (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, has_deriv_at (λ x, F x a) (F' x a) x) :
  has_deriv_at (λn, ∫ a, F n a ∂μ) (∫ a, F' x₀ a ∂μ) x₀ :=
begin
  have x₀_in : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos,
  have diff_x₀ : ∀ᵐ a ∂μ, has_deriv_at (λ x, F x a) (F' x₀ a) x₀ :=
    h_diff.mono (λ a ha, ha x₀ x₀_in),
  have : ∀ᵐ a ∂μ, lipschitz_on_with (nnreal.abs (bound a)) (ball x₀ ε) (λ (x : ℝ), F x a),
  { apply (h_diff.and h_bound).mono,
    rintros a ⟨ha_deriv, ha_bound⟩,
    have bound_nonneg : 0 ≤ bound a := (norm_nonneg (F' x₀ a)).trans (ha_bound x₀ x₀_in),
    rw lipschitz_on_with_iff_dist_le_mul,
    intros x y x_in y_in,
    simp_rw dist_eq_norm,
    convert convex.norm_image_sub_le_of_norm_has_deriv_within_le
      (λ y y_in, (ha_deriv y y_in).has_deriv_within_at)
      (λ y y_in, ha_bound y y_in) (convex_ball _ _) y_in x_in,
    rw [nnreal.coe_abs, abs_of_nonneg bound_nonneg] },
  exact has_deriv_at_of_dominated_loc_of_lip ε_pos hF_meas hF_int (hF'_meas _ x₀_in) this
        bound_measurable bound_integrable diff_x₀
end
lemma has_deriv_at_of_dominated_loc_of_deriv_le' {F : ℝ → α → E} {F' : ℝ → α → E} {x₀ : ℝ}
  {s : set α} {bound : α → ℝ} {ε : ℝ}
  (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠ x in 𝓝 x₀, measurable (F x))
  (hF_int : integrable (F x₀) μ)
  (hF'_meas : ∀ x ∈ ball x₀ ε, measurable (F' x))
  (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, ∥F' x a∥ ≤ bound a)
  (bound_measurable : measurable (bound : α → ℝ))
  (bound_integrable : integrable bound μ)
  (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, has_deriv_at (λ x, F x a) (F' x a) x) :
  has_deriv_at (λn, ∫ a, F n a ∂μ) (∫ a, F' x₀ a ∂μ) x₀ :=
begin
  have x₀_in : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos,
  have diff_x₀ : ∀ᵐ a ∂μ, has_deriv_at (λ x, F x a) (F' x₀ a) x₀ :=
    h_diff.mono (λ a ha, ha x₀ x₀_in),
  have : ∀ᵐ a ∂μ, lipschitz_on_with (nnreal.abs (bound a)) (ball x₀ ε) (λ (x : ℝ), F x a),
  { apply (h_diff.and h_bound).mono,
    rintros a ⟨ha_deriv, ha_bound⟩,
    have bound_nonneg : 0 ≤ bound a := (norm_nonneg (F' x₀ a)).trans (ha_bound x₀ x₀_in),
    rw lipschitz_on_with_iff_dist_le_mul,
    intros x y x_in y_in,
    simp_rw dist_eq_norm,
    convert convex.norm_image_sub_le_of_norm_has_deriv_within_le
      (λ y y_in, (ha_deriv y y_in).has_deriv_within_at)
      (λ y y_in, ha_bound y y_in) (convex_ball _ _) y_in x_in,
    rw [nnreal.coe_abs, abs_of_nonneg bound_nonneg] },
  exact has_deriv_at_of_dominated_loc_of_lip ε_pos hF_meas hF_int (hF'_meas _ x₀_in) this
        bound_measurable bound_integrable diff_x₀
end

#exit

variables {H : Type*} [normed_group H] [normed_space ℝ H]
  [second_countable_topology $ H →L[ℝ] E] [measurable_space $ H →L[ℝ] E]
  [borel_space $ H →L[ℝ] E]

lemma has_fderiv_at_of_dominated {F : H → α → E} {F' : H → α → (H →L[ℝ] E)} {x₀ : H} {bound : α → ℝ}
  (hF_meas : ∀ᶠ x in 𝓝 x₀, measurable (F x))
  (hF_int : ∀ᶠ x in 𝓝 x₀, integrable (F x) μ)
  (hF'_meas : ∀ᶠ x in 𝓝 x₀, measurable (F' x))
  (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ a ∂μ, ∥F' x a∥ ≤ bound a)
  (bound_integrable : integrable bound μ)
  (h_diff : ∀ᵐ a ∂μ, has_fderiv_at (λ x, F x a) (F' x₀ a) x₀) :
  has_fderiv_at (λn, ∫ a, F n a ∂μ) (∫ a, F' x₀ a ∂μ) x₀ :=
begin

  sorry
end
