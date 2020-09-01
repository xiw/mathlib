import measure_theory.set_integral

noncomputable theory

open topological_space measure_theory filter metric
open_locale topological_space filter nnreal big_operators

section
variables {𝕜 : Type*} [normed_field 𝕜]
          {E : Type*} [normed_group E] [normed_space 𝕜 E]
          {F : Type*} [normed_group F] [normed_space 𝕜 F]

lemma continuous_linear_map.map_sum (L : E →L[𝕜] F) {ι : Type*} (s : finset ι) (g : ι → E) :
  L (∑ i in s, g i) = ∑ i in s, L (g i) := L.to_linear_map.map_sum

end

section
variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
          {E : Type*} [normed_group E] [normed_space 𝕜 E]
          {F : Type*} [normed_group F] [normed_space 𝕜 F]

lemma continuous_of_linear_of_bound {f : E → F} (h_add : ∀ x y, f (x + y) = f x + f y)
  (h_smul : ∀ (c : 𝕜) x, f (c • x) = c • f x) {C : ℝ} (h_bound : ∀ x, ∥f x∥ ≤ C*∥x∥) :
  continuous f :=
let φ : E →ₗ[𝕜] F := ⟨f, h_add, h_smul⟩ in φ.continuous_of_bound C h_bound

end

variables {α : Type*} [measurable_space α] {μ : measure α}
variables {E : Type*} [normed_group E] [second_countable_topology E] [normed_space ℝ E]
          [complete_space E] [measurable_space E] [borel_space E]
variables {F : Type*} [normed_group F] [second_countable_topology F] [normed_space ℝ F]
  [complete_space F] [measurable_space F] [borel_space F]

-- See mathlib PR #3978
lemma integrable.induction (P : (α → E) → Prop)
  (h_ind : ∀ (c : E) ⦃s⦄, is_measurable s → μ s < ⊤ → P (s.indicator (λ _, c)))
  (h_sum : ∀ ⦃f g⦄, measurable f → measurable g → integrable f μ → integrable g μ → P f → P g → P (f + g))
  (h_closed : is_closed {f : α →₁[μ] E | P f} )
  (h_ae : ∀ ⦃f g⦄, f =ᵐ[μ] g → measurable f → integrable f μ → measurable g → P f → P g) :
  ∀ ⦃f : α → E⦄ (hf : measurable f) (h2f : integrable f μ), P f :=
sorry

-- borel_space.lean, next to measurable.const_smul
lemma measurable.const_mul {f : α → ℝ} (h : measurable f) (c : ℝ) : measurable (λ x, c*f x) :=
(measurable.const_smul h c : _)

lemma measurable.mul_const {f : α → ℝ} (h : measurable f) (c : ℝ) : measurable (λ x, f x*c) :=
by simp only [h.const_mul c, mul_comm]

lemma continuous_linear_map.measurable (L : E →L[ℝ] F) : measurable L :=
L.continuous.measurable

lemma measurable.clm_apply {φ : α → E} (φ_meas : measurable φ)
  (L : E →L[ℝ] F) : measurable (λ (a : α), L (φ a)) :=
L.measurable.comp φ_meas

namespace measure_theory

-- l1_space.lean, next to integrable.smul
lemma integrable.const_mul {f : α → ℝ} (h : integrable f μ) (c : ℝ) : integrable (λ x, c*f x) μ :=
(integrable.smul c h : _)

lemma integrable.mul_const {f : α → ℝ} (h : integrable f μ) (c : ℝ) : integrable (λ x, f x * c) μ :=
by simp_rw [mul_comm, h.const_mul _]



lemma l1.continuous_integral : continuous (λ (f : α →₁[μ] E), f.integral) :=
by simp [l1.integral, l1.integral_clm.continuous]

lemma l1.integral_eq_integral (f : α →₁[μ] E) : f.integral =  ∫ a, f a ∂μ :=
by rw [integral_eq, l1.of_fun_to_fun]

@[simp] lemma l1.integral_of_fun_eq_integral {f : α → E} (f_m : measurable f) (f_i : integrable f μ) :
  ∫ a, (l1.of_fun f f_m f_i) a ∂μ = ∫ a, f a ∂μ :=
integral_congr_ae (l1.measurable _) f_m (l1.to_fun_of_fun f f_m f_i)

lemma continuous_integral : continuous (λ (f : α →₁[μ] E), ∫ a, f a ∂μ) :=
begin
  convert l1.continuous_integral,
  ext f,
  rw l1.integral_eq_integral
end

-- next to measure_theory.integral_indicator in set_integral.lean
lemma integral_indicator_const
  {α E : Type*}
  [measurable_space α]
  {μ : measure α}
  [normed_group E]
  [second_countable_topology E]
  [normed_space ℝ E]
  [complete_space E]
  [measurable_space E]
  [borel_space E]
  (e : E)
  ⦃s : set α⦄
  (s_meas : is_measurable s)
  (s_finite : μ s < ⊤) :
    ∫ (a : α), s.indicator (λ (_x : α), e) a ∂μ = (μ s).to_real • e :=
begin
  rw measure_theory.integral_indicator (measurable_const : measurable (λ x, e)) s_meas,
  change ∫ (x : α) in s, e ∂μ = (μ s).to_real • e,
  rw measure_theory.set_integral_const,
end

lemma l1.norm_eq_integral_norm (f : α →₁[μ] E) : ∥f∥ = ∫ a, ∥f a∥ ∂μ :=
begin
  rw l1.norm_eq_norm_to_fun,
  rw integral_eq_lintegral_of_nonneg_ae,
  apply eventually_of_forall,
  intros a,
  simp [norm_nonneg],
  exact continuous_norm.measurable.comp f.measurable
end

lemma l1.measurable_norm (f : α →₁[μ] E) : measurable (λ a, ∥f a∥) :=
f.measurable.norm

lemma l1.integrable_norm (f : α →₁[μ] E) : integrable (λ a, ∥f a∥) μ :=
(integrable_norm_iff _).mpr f.integrable

lemma l1.norm_of_fun_eq_integral_norm {f : α → E} (f_m : measurable f) (f_i : integrable f μ) :
  ∥l1.of_fun f f_m f_i∥ = ∫ a, ∥f a∥ ∂μ :=
begin
  rw l1.norm_eq_integral_norm,
  refine integral_congr_ae (l1.measurable_norm _) f_m.norm _,
  apply (l1.to_fun_of_fun f f_m f_i).mono,
  intros a ha,
  simp [ha]
end

lemma integrable.clm_apply {φ : α → E} (φ_int : integrable φ μ)
  (L : E →L[ℝ] F) : integrable (λ (a : α), L (φ a)) μ :=
((integrable.norm φ_int).const_mul ∥L∥).mono' (eventually_of_forall $ λ a, L.le_op_norm (φ a))

def l1.clm_apply (φ : α →₁[μ] E) (L : E →L[ℝ] F) : α →₁[μ] F :=
l1.of_fun (λ a, L (φ a)) (φ.measurable.clm_apply L) (φ.integrable.clm_apply L)

lemma l1.clm_apply_apply (φ : α →₁[μ] E) (L : E →L[ℝ] F) : ∀ᵐ a ∂μ, (φ.clm_apply L) a = L (φ a) :=
l1.to_fun_of_fun _ _ _

-- The next lemma is a bit silly since the conclusion holds everywhere, but this weakening is
-- useful
lemma l1.norm_clm_apply_le (φ : α →₁[μ] E) (L : E →L[ℝ] F) : ∀ᵐ a ∂μ, ∥L (φ a)∥ ≤ ∥L∥*∥φ a∥ :=
eventually_of_forall (λ a, L.le_op_norm (φ a))

lemma l1.measurable_clm_apply (L : E →L[ℝ] F) (φ : α →₁[μ] E): measurable (φ.clm_apply L) :=
(φ.clm_apply L).measurable

lemma l1.measurable_clm_apply' (L : E →L[ℝ] F) (φ : α →₁[μ] E): measurable (λ a, L (φ a)) :=
L.measurable.comp φ.measurable

lemma l1.integrable_clm_apply (L : E →L[ℝ] F) (φ : α →₁[μ] E): integrable (φ.clm_apply L) μ :=
(φ.clm_apply L).integrable

lemma l1.integrable_clm_apply' (L : E →L[ℝ] F) (φ : α →₁[μ] E): integrable (λ a, L (φ a)) μ :=
φ.integrable.clm_apply L

lemma l1.integral_clm_apply (φ : α →₁[μ] E) (L : E →L[ℝ] F):
  ∫ a, (φ.clm_apply L) a ∂μ = ∫ a, L (φ a) ∂μ :=
by simp [l1.clm_apply]

def l1.clm_applyₗ (L : E →L[ℝ] F) : (α →₁[μ] E) →ₗ[ℝ] (α →₁[μ] F) :=
{ to_fun := λ φ, φ.clm_apply L,
  map_add' := begin
    intros f g,
    dsimp [l1.clm_apply],
    rw [← l1.of_fun_add, l1.of_fun_eq_of_fun],
    apply (l1.add_to_fun f g).mono,
    intros a ha,
    simp only [ha, pi.add_apply, L.map_add]
  end,
  map_smul' := begin
    intros c f,
    dsimp [l1.clm_apply],
    rw [← l1.of_fun_smul, l1.of_fun_eq_of_fun],
    apply (l1.smul_to_fun c f).mono,
    intros a ha,
    simp only [ha, pi.smul_apply, continuous_linear_map.map_smul]
  end }

lemma l1.clm_apply_norm_le (φ : α →₁[μ] E) (L : E →L[ℝ] F) : ∥φ.clm_apply L∥ ≤ ∥L∥*∥φ∥ :=
begin
  erw l1.norm_of_fun_eq_integral_norm,
  calc
  ∫ a, ∥L (φ a)∥ ∂μ ≤ ∫ a, ∥L∥ *∥φ a∥ ∂μ : integral_mono (L.measurable.comp φ.measurable).norm
                                (φ.integrable_clm_apply' L).norm (φ.measurable_norm.const_mul $ ∥L∥)
                                (φ.integrable_norm.const_mul $ ∥L∥) (φ.norm_clm_apply_le L)
  ... = ∥L∥ * ∥φ∥ : by rw [integral_mul_left, φ.norm_eq_integral_norm]
end

end measure_theory

open measure_theory

variables (μ)

def continuous_linear_map.l1_apply (L : E →L[ℝ] F) : (α →₁[μ] E) →L[ℝ] (α →₁[μ] F) :=
linear_map.mk_continuous (measure_theory.l1.clm_applyₗ L) (∥L∥) (λ φ, φ.clm_apply_norm_le L)

lemma continuous_linear_map.continuous_integral_apply (L : E →L[ℝ] F) :
continuous (λ (φ : α →₁[μ] E), ∫ (a : α), L (φ a) ∂μ) :=
begin
  rw ← funext (λ φ : α →₁[μ] E, φ.integral_clm_apply L),
  exact continuous_integral.comp (L.l1_apply μ).continuous
end

variables {μ}

lemma continuous_linear_map.integral_apply_comm {φ : α → E} (L : E →L[ℝ] F) (φ_meas : measurable φ)
  (φ_int : integrable φ μ) : ∫ a, L (φ a) ∂μ = L (∫ a, φ a ∂μ) :=
begin
  apply integrable.induction (λ φ, ∫ a, L (φ a) ∂μ = L (∫ a, φ a ∂μ)) _ _ _ _ φ_meas φ_int,
  { intros e s s_meas s_finite,
    rw [integral_indicator_const e s_meas s_finite, continuous_linear_map.map_smul,
        ← integral_indicator_const (L e) s_meas s_finite],
    congr' 1,
    ext a,
    rw set.indicator_comp_of_zero L.map_zero },
  { intros f g f_meas g_meas f_int g_int hf hg,
    simp [L.map_add, integral_add f_meas f_int g_meas g_int,
      integral_add (f_meas.clm_apply L) (f_int.clm_apply L)
      (g_meas.clm_apply L) (g_int.clm_apply L), hf, hg] },
  { exact is_closed_eq (L.continuous_integral_apply μ)  (L.continuous.comp continuous_integral) },
  { intros f g hfg f_meas f_int g_meas hf,
    convert hf using 1 ; clear hf,
    { exact integral_congr_ae (L.measurable.comp g_meas) (L.measurable.comp f_meas) (hfg.fun_comp L).symm },
    { rw integral_congr_ae g_meas f_meas hfg.symm } }
end

lemma continuous_linear_map.l1_integral_apply_comm (L : E →L[ℝ] F) (φ : α →₁[μ] E) :
  ∫ a, L (φ a) ∂μ = L (∫ a, φ a ∂μ) :=
L.integral_apply_comm φ.measurable φ.integrable
