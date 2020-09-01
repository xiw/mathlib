import measure_theory.interval_integral
import measure_theory.clm
import analysis.calculus.mean_value

noncomputable theory

open topological_space measure_theory filter first_countable_topology metric
open_locale topological_space filter nnreal big_operators


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

/-! # linear map -/

section

variables (R M₂ : Type*) { M: Type*} [comm_ring R] [add_comm_monoid M] [semimodule R M]
          [add_comm_monoid M₂] [semimodule R M₂]

def linear_map.applyₗ (v : M) : (M →ₗ[R] M₂) →ₗ[R] M₂ :=
{ to_fun := λ f, f v,
  map_add' := λ f g, f.add_apply g v,
  map_smul' := λ x f, f.smul_apply x v }

end

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

/-! # Normed groups -/

section
variables {E : Type*} [normed_group E] {F : Type*} [normed_group F]

lemma normed_space.tendsto_nhds_nhds {f : E → F} {x : E} {y : F} :
  tendsto f (𝓝 x) (𝓝 y) ↔ ∀ ε > 0, ∃ δ > 0, ∀ x', ∥x' - x∥ < δ → ∥f x' - y∥ < ε :=
by simp_rw [metric.tendsto_nhds_nhds, dist_eq_norm]

lemma lipschitz_on_with_iff_norm_sub_le {f : E → F} {C : ℝ≥0} {s : set E} :
  lipschitz_on_with C s f ↔  ∀ {x y : E}, x ∈ s → y ∈ s →  ∥f x - f y∥ ≤ C * ∥x - y∥ :=
by simp only [lipschitz_on_with_iff_dist_le_mul, dist_eq_norm]

lemma lipschitz_on_with.norm_sub_le {f : E → F} {C : ℝ≥0} {s : set E} (h : lipschitz_on_with C s f)
{x y : E} (x_in : x ∈ s) (y_in : y ∈ s) : ∥f x - f y∥ ≤ C * ∥x - y∥ :=
lipschitz_on_with_iff_norm_sub_le.mp h x_in y_in

lemma eq_of_norm_sub_eq_zero {u v : E} (h : ∥u - v∥ = 0) : u = v :=
begin
  apply eq_of_dist_eq_zero,
  rwa dist_eq_norm
end

lemma norm_le_insert (u v : E) : ∥v∥ ≤ ∥u∥ + ∥u - v∥ :=
calc ∥v∥ = ∥u - (u - v)∥ : by abel
... ≤ ∥u∥ + ∥u - v∥ : norm_sub_le u _

end


/-! # Real normed space -/
section
variables {E : Type*} [normed_group E] [normed_space ℝ E]
lemma mul_norm_of_nonneg {t : ℝ} (ht : 0 ≤ t) (x : E) : t*∥x∥ = ∥t • x∥ :=
by rw [norm_smul, real.norm_eq_abs, abs_of_nonneg ht]

end

/-! # Calculus -/

section
variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
          {E : Type*} [normed_group E] [normed_space 𝕜 E]
          {F : Type*} [normed_group F] [normed_space 𝕜 F]

lemma op_norm_le_of_ball {f : E →L[𝕜] F} {ε : ℝ} {C : ℝ} (ε_pos : 0 < ε) (hC : 0 ≤ C)
  (hf : ∀ x ∈ ball (0 : E) ε, ∥f x∥ ≤ C * ∥x∥ ) : ∥f∥ ≤ C :=
begin
  apply f.op_norm_le_bound hC,
  intros x,
  rcases normed_field.exists_one_lt_norm 𝕜 with ⟨c, hc⟩,
  by_cases hx : x = 0, { simp [hx] },
  rcases rescale_to_shell hc (half_pos ε_pos) hx with ⟨δ, hδ, δxle, leδx, δinv⟩,
  have δx_in : δ • x ∈ ball (0 : E) ε,
  { rw [mem_ball, dist_eq_norm, sub_zero],
    linarith },
  calc ∥f x∥ = ∥f ((1/δ) • δ • x)∥ : by simp [hδ, smul_smul]
  ... = ∥1/δ∥ * ∥f (δ • x)∥ : by simp [norm_smul]
  ... ≤ ∥1/δ∥ * (C*∥δ • x∥) : mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  ... = C * ∥x∥ : by { rw norm_smul, field_simp [hδ], ring },
  exact hf _ δx_in
end

lemma op_norm_eq_of_bounds {φ : E →L[𝕜] F} {M : ℝ} (M_nonneg : 0 ≤ M)
  (h_above : ∀ x, ∥φ x∥ ≤ M*∥x∥) (h_below : ∀ N ≥ 0, (∀ x, ∥φ x∥ ≤ N*∥x∥) → M ≤ N) :
  ∥φ∥ = M :=
le_antisymm (φ.op_norm_le_bound M_nonneg h_above)
  ((le_cInf_iff continuous_linear_map.bounds_bdd_below ⟨M, M_nonneg, h_above⟩).mpr $
   λ N ⟨N_nonneg, hN⟩, h_below N N_nonneg hN)


@[simp]
lemma continuous_linear_map.norm_smul_right_apply (c : E →L[𝕜] 𝕜) (f : F) : ∥c.smul_right f∥ = ∥c∥ * ∥f∥ :=
begin
  by_cases hf : f = 0,
  { simp [hf] },
  replace hf : 0 < ∥f∥ := norm_pos_iff.mpr hf,
  apply op_norm_eq_of_bounds (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (λ e, calc  ∥c.smul_right f e∥  = ∥c e∥ * ∥f∥ : by simp [norm_smul]
            ... ≤ ∥c∥ * ∥e∥ * ∥f∥ : mul_le_mul_of_nonneg_right (c.le_op_norm e) (norm_nonneg _)
            ... = ∥c∥*∥f∥*∥e∥  : by ring),
  intros N N_nonneg hN,
  suffices : ∥c∥ ≤ N/∥f∥, by rwa ← le_div_iff hf,
  apply c.op_norm_le_bound (div_nonneg N_nonneg $ norm_nonneg _),
  intros x,
  rw [div_mul_eq_mul_div, le_div_iff hf],
  simpa [norm_smul] using hN x
end

def continuous_linear_map.smul_rightₗ (c : E →L[𝕜] 𝕜) : F →ₗ[𝕜] (E →L[𝕜] F) :=
{ to_fun := c.smul_right,
  map_add' := λ x y, by { ext e, simp [smul_add] },
  map_smul' := λ a x, by { ext e, simp [smul_comm] } }

noncomputable
def continuous_linear_map.smul_rightL (c : E →L[𝕜] 𝕜) : F →L[𝕜] (E →L[𝕜] F) :=
(c.smul_rightₗ : F →ₗ[𝕜] (E →L[𝕜] F)).mk_continuous _ (λ f, le_of_eq $ c.norm_smul_right_apply f)

@[simp]
lemma continuous_linear_map.norm_smul_right (c : E →L[𝕜] 𝕜) (hF : 0 < vector_space.dim 𝕜 F) :
  ∥(c.smul_rightL : F →L[𝕜] (E →L[𝕜] F))∥ = ∥c∥ :=
continuous_linear_map.homothety_norm hF _ (norm_nonneg _) c.norm_smul_right_apply

variables (𝕜 F)

/-- The linear map obtained by applying a continuous linear map at a given vector. -/
def continuous_linear_map.applyₗ (v : E) : (E →L[𝕜] F) →ₗ[𝕜] F :=
{ to_fun := λ f, f v,
  map_add' := λ f g, f.add_apply g v,
  map_smul' := λ x f, f.smul_apply x v }

lemma continuous_linear_map.continuous_apply (v : E) : continuous (continuous_linear_map.applyₗ 𝕜 F v) :=
begin
  apply (continuous_linear_map.applyₗ 𝕜 F v).continuous_of_bound,
  intro f,
  rw mul_comm,
  exact f.le_op_norm v,
end

/-- The continuous linear map obtained by applying a continuous linear map at a given vector. -/
noncomputable def continuous_linear_map.apply (v : E) : (E →L[𝕜] F) →L[𝕜] F :=
⟨continuous_linear_map.applyₗ 𝕜 F v, continuous_linear_map.continuous_apply _ _ _⟩

variables {𝕜 F}

lemma has_fderiv_at.le_of_lip {f : E → F} {f' : E →L[𝕜] F} {x₀ : E} (hf: has_fderiv_at f f' x₀)
  {s : set E} (he : s ∈ 𝓝 x₀) {C : ℝ≥0} (hlip : lipschitz_on_with C s f) : ∥f'∥ ≤ C :=
begin
  replace hf : ∀ ε > 0, ∃ δ > 0, ∀ x', ∥x' - x₀∥ < δ → ∥x' - x₀∥⁻¹ * ∥f x' - f x₀ - f' (x' - x₀)∥ < ε,
    by simpa [has_fderiv_at_iff_tendsto, normed_space.tendsto_nhds_nhds] using hf,
  obtain ⟨ε, ε_pos, hε⟩ : ∃ ε > 0, ball x₀ ε ⊆ s := mem_nhds_iff.mp he,
  apply real.le_of_forall_epsilon_le,
  intros η η_pos,
  rcases hf η η_pos with ⟨δ, δ_pos, h⟩, clear hf,
  apply op_norm_le_of_ball (lt_min ε_pos δ_pos) (by linarith [C.coe_nonneg]: (0 : ℝ) ≤ C + η),
  intros u u_in,
  let x := x₀ + u,
  rw show u = x - x₀, by rw [add_sub_cancel'],
  have xε : x ∈ ball x₀ ε,
    by simpa [dist_eq_norm] using ball_subset_ball (min_le_left ε δ) u_in,
  have xδ : ∥x - x₀∥ < δ,
    by simpa [dist_eq_norm] using ball_subset_ball (min_le_right ε δ) u_in,
  replace h : ∥f x - f x₀ - f' (x - x₀)∥ ≤ η*∥x - x₀∥,
  { by_cases H : x - x₀ = 0,
    { simp [eq_of_sub_eq_zero H] },
    { exact (inv_mul_le_iff' $ norm_pos_iff.mpr H).mp (le_of_lt $ h x xδ) } },
  have := hlip.norm_sub_le (hε xε) (hε $ mem_ball_self ε_pos),
  calc ∥f' (x - x₀)∥ ≤ ∥f x - f x₀∥ + ∥f x - f x₀ - f' (x - x₀)∥ : norm_le_insert _ _
  ... ≤ (C + η) * ∥x - x₀∥ : by linarith,
end


end

variables {α : Type*} [measurable_space α] {μ : measure α}


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
    apply bound_integrable.norm.const_mul },
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


variables {H : Type*} [normed_group H] [normed_space ℝ H] [measurable_space H]

  [second_countable_topology $ H →L[ℝ] E] [measurable_space $ H →L[ℝ] E]
  [borel_space $ H →L[ℝ] E]

lemma measurable.apply_continuous_linear_map {φ : α → H →L[ℝ] E} (hφ : measurable φ) (v : H) :
  measurable (λ a, φ a v) :=
(continuous_linear_map.continuous_apply _ _ v).measurable.comp hφ

lemma measure_theory.integrable.apply_continuous_linear_map {φ : α → H →L[ℝ] E}
  (φ_meas : measurable φ) (φ_int : integrable φ μ) (v : H) : integrable (λ a, φ a v) μ :=
begin
  apply (φ_int.norm.mul_const _).mono',
  apply eventually_of_forall,
  intro a,
  exact (φ a).le_op_norm v,
end

lemma continuous_linear_map.apply_integral {φ : α → H →L[ℝ] E} (φ_meas : measurable φ)
  (φ_int : integrable φ μ) (v : H) : ∫ a, φ a v ∂μ = (∫ a, φ a ∂μ) v :=
(continuous_linear_map.apply ℝ E v).integral_apply_comm φ_meas φ_int

lemma measurable_abs : measurable (abs : ℝ → ℝ) :=
real.continuous_abs.measurable

lemma has_fderiv_at_of_dominated_of_lip {F : H → α → E} {F' : α → (H →L[ℝ] E)} {x₀ : H}
  {bound : α → ℝ}
  {ε : ℝ}
  (ε_pos : 0 < ε)
  (hF_meas : ∀ x ∈ ball x₀ ε, measurable (F x))
  (hF_int : integrable (F x₀) μ)
  (hF'_meas : measurable F')
  (h_lipsch : ∀ᵐ a ∂μ, lipschitz_on_with (nnreal.abs $ bound a) (ball x₀ ε) (λ x, F x a))
  (bound_measurable : measurable (bound : α → ℝ))
  (bound_integrable : integrable (bound : α → ℝ) μ)
  (h_diff : ∀ᵐ a ∂μ, has_fderiv_at (λ x, F x a) (F' a) x₀) :
  has_fderiv_at (λ x, ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀ :=
begin
  have x₀_in : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos,
  have nneg : ∀ x, 0 ≤ ∥x - x₀∥⁻¹ := λ x, inv_nonneg.mpr (norm_nonneg _) ,
  set b : α → ℝ := λ a, abs (bound a),
  have b_meas : measurable b :=  measurable_abs.comp bound_measurable,
  have b_int : integrable b μ := bound_integrable.norm,
  have b_nonneg : ∀ a, 0 ≤ b a := λ a, abs_nonneg _,
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
  have hF'_int : integrable F' μ,
  { have : ∀ᵐ a ∂μ, ∥F' a∥ ≤ b a,
    { apply (h_diff.and h_lipsch).mono,
      rintros a ⟨ha_diff, ha_lip⟩,
      exact ha_diff.le_of_lip (ball_mem_nhds _ ε_pos) ha_lip },
    exact b_int.mono' this },
  have h_ball: ball x₀ ε ∈ 𝓝 x₀ := ball_mem_nhds x₀ ε_pos,
  have : ∀ᶠ x in 𝓝 x₀,
      ∥x - x₀∥⁻¹ * ∥∫ a, F x a ∂μ - ∫ a, F x₀ a ∂μ - (∫ a, F' a ∂μ) (x - x₀)∥ =
       ∥∫ a, ∥x - x₀∥⁻¹ • (F x a - F x₀ a  - F' a (x - x₀)) ∂μ∥,
  { apply mem_sets_of_superset (ball_mem_nhds _ ε_pos),
    intros x x_in,
    rw [set.mem_set_of_eq, mul_norm_of_nonneg (nneg _), integral_smul,
        integral_sub, integral_sub, continuous_linear_map.apply_integral hF'_meas hF'_int],
    exacts [hF_meas _ x_in,
            hF_int' x x_in,
            hF_meas _ x₀_in,
            hF_int,
            (hF_meas _ x_in).sub (hF_meas _ x₀_in),
            (hF_int' x x_in).sub (hF_meas _ x_in) (hF_meas _ x₀_in) hF_int,
            hF'_meas.apply_continuous_linear_map _,
            hF'_int.apply_continuous_linear_map hF'_meas _] },
  rw [has_fderiv_at_iff_tendsto, tendsto_congr' this, ← tendsto_zero_iff_norm_tendsto_zero,
      ← show ∫ (a : α), ∥x₀ - x₀∥⁻¹ • (F x₀ a - F x₀ a - (F' a) (x₀ - x₀)) ∂μ = 0, by simp],
  apply tendsto_integral_filter_of_dominated_convergence,
  { apply is_countably_generated_nhds },
  { filter_upwards [h_ball],
    intros x x_in,
    apply measurable.const_smul,
    exact ((hF_meas _ x_in).sub (hF_meas _ x₀_in)).sub (hF'_meas.apply_continuous_linear_map _) },
  { simp [measurable_const] },
  { apply mem_sets_of_superset h_ball,
    intros x hx,
    apply (h_diff.and h_lipsch).mono,
    rintros a ⟨ha_deriv, ha_bound⟩,
    show ∥∥x - x₀∥⁻¹ • (F x a - F x₀ a - F' a (x - x₀))∥ ≤ b a + ∥F' a∥,
    replace ha_bound : ∥F x a - F x₀ a∥ ≤ b a * ∥x - x₀∥,
    { rw lipschitz_on_with_iff_dist_le_mul at ha_bound,
      simpa [← dist_eq_norm] using ha_bound _ _ hx x₀_in },
    calc ∥∥x - x₀∥⁻¹ • (F x a - F x₀ a - F' a (x - x₀))∥
    = ∥∥x - x₀∥⁻¹ • (F x a - F x₀ a) - ∥x - x₀∥⁻¹ • F' a (x - x₀)∥ : by rw smul_sub
    ... ≤  ∥∥x - x₀∥⁻¹ • (F x a - F x₀ a)∥ + ∥∥x - x₀∥⁻¹ • F' a (x - x₀)∥ : norm_sub_le _ _
    ... =  ∥x - x₀∥⁻¹ * ∥F x a - F x₀ a∥ + ∥x - x₀∥⁻¹ * ∥F' a (x - x₀)∥ : by { rw [mul_norm_of_nonneg, mul_norm_of_nonneg] ; exact nneg _}
    ... ≤  ∥x - x₀∥⁻¹ * (b a * ∥x - x₀∥) + ∥x - x₀∥⁻¹ * (∥F' a∥ * ∥x - x₀∥) : add_le_add _ _
    ... ≤ b a + ∥F' a∥ : _,
    exact mul_le_mul_of_nonneg_left ha_bound (nneg _),
    apply mul_le_mul_of_nonneg_left ((F' a).le_op_norm _) (nneg _),
    by_cases h : ∥x - x₀∥ = 0,
    { simpa [h] using add_nonneg (b_nonneg a) (norm_nonneg (F' a)) },
    { field_simp [h] } },
  { exact integrable.add b_meas b_int hF'_meas.norm hF'_int.norm },
  { apply h_diff.mono,
    intros a ha,
    suffices : tendsto (λ x, ∥x - x₀∥⁻¹ • (F x a - F x₀ a - F' a (x - x₀))) (𝓝 x₀) (𝓝 0),
    by simpa,
    rw tendsto_zero_iff_norm_tendsto_zero,
    have : (λ x, ∥x - x₀∥⁻¹ * ∥F x a - F x₀ a - F' a (x - x₀)∥) = λ x, ∥∥x - x₀∥⁻¹ • (F x a - F x₀ a - F' a (x - x₀))∥,
    { ext x,
      rw mul_norm_of_nonneg (nneg _) },
    rwa [has_fderiv_at_iff_tendsto, this] at ha },
end


instance : measurable_space (ℝ →L[ℝ] E) := borel _
instance : borel_space (ℝ →L[ℝ] E) := ⟨rfl⟩

instance : second_countable_topology (ℝ →L[ℝ] E) := sorry

lemma has_deriv_at_of_dominated_loc_of_lip'' {F : ℝ → α → E} {F' : α → E} {x₀ : ℝ} {bound : α → ℝ}
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
  simp_rw has_deriv_at_iff_has_fderiv_at at h_diff ⊢,
  have := ((1 : ℝ →L[ℝ] ℝ).smul_rightL : E →L[ℝ] _).integral_apply_comm hF'_meas sorry,
  change has_fderiv_at (λ (x : ℝ), integral μ (F x)) ((1 : ℝ →L[ℝ] ℝ).smul_rightL (∫ a, F' a ∂μ)) x₀,
  rw ← this,
  exact has_fderiv_at_of_dominated_of_lip ε_pos hF_meas hF_int
    ((1 : ℝ →L[ℝ] ℝ).smul_rightL.continuous.measurable.comp hF'_meas) h_lipsch
    bound_measurable bound_integrable h_diff
end
end
