/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.normed_space.hahn_banach

/-!
# The topological dual of a normed space

In this file we define the topological dual of a normed space, and the bounded linear map from
a normed space into its double dual.

We also prove that, for base field such as the real or the complex numbers, this map is an isometry.
More generically, this is proved for any field in the class `has_exists_extension_norm_eq`, i.e.,
satisfying the Hahn-Banach theorem.
-/

noncomputable theory
universes u v

namespace normed_space

section general
variables (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
variables (E : Type*) [normed_group E] [normed_space 𝕜 E]

/-- The topological dual of a normed space `E`. -/
@[derive [has_coe_to_fun, normed_group, normed_space 𝕜]] def dual := E →L[𝕜] 𝕜

instance : inhabited (dual 𝕜 E) := ⟨0⟩

/-- The inclusion of a normed space in its double (topological) dual. -/
def inclusion_in_double_dual' (x : E) : (dual 𝕜 (dual 𝕜 E)) :=
linear_map.mk_continuous
  { to_fun := λ f, f x,
    map_add'    := by simp,
    map_smul'   := by simp }
  ∥x∥
  (λ f, by { rw mul_comm, exact f.le_op_norm x } )

@[simp] lemma dual_def (x : E) (f : dual 𝕜 E) :
  ((inclusion_in_double_dual' 𝕜 E) x) f = f x := rfl

lemma double_dual_bound (x : E) : ∥(inclusion_in_double_dual' 𝕜 E) x∥ ≤ ∥x∥ :=
begin
  apply continuous_linear_map.op_norm_le_bound,
  { simp },
  { intros f, rw mul_comm, exact f.le_op_norm x, }
end

/-- The inclusion of a normed space in its double (topological) dual, considered
   as a bounded linear map. -/
def inclusion_in_double_dual : E →L[𝕜] (dual 𝕜 (dual 𝕜 E)) :=
linear_map.mk_continuous
  { to_fun := λ (x : E), (inclusion_in_double_dual' 𝕜 E) x,
    map_add'    := λ x y, by { ext, simp },
    map_smul'   := λ (c : 𝕜) x, by { ext, simp } }
  1
  (λ x, by { convert double_dual_bound _ _ _, simp } )

end general

section bidual_isometry

variables {𝕜 : Type v} [nondiscrete_normed_field 𝕜] [normed_algebra ℝ 𝕜]
[has_exists_extension_norm_eq.{u} 𝕜]
{E : Type u} [normed_group E] [normed_space 𝕜 E]

/-- If one controls the norm of every `f x`, then one controls the norm of `x`.
    Compare `continuous_linear_map.op_norm_le_bound`. -/
lemma norm_le_dual_bound (x : E) {M : ℝ} (hMp: 0 ≤ M) (hM : ∀ (f : dual 𝕜 E), ∥f x∥ ≤ M * ∥f∥) :
  ∥x∥ ≤ M :=
begin
  classical,
  by_cases h : x = 0,
  { simp only [h, hMp, norm_zero] },
  { obtain ⟨f, hf⟩ : ∃ g : E →L[𝕜] 𝕜, _ := exists_dual_vector x h,
    calc ∥x∥ = ∥norm' 𝕜 x∥ : (norm_norm' _ _ _).symm
    ... = ∥f x∥ : by rw hf.2
    ... ≤ M * ∥f∥ : hM f
    ... = M : by rw [hf.1, mul_one] }
end

/-- The inclusion of a real normed space in its double dual is an isometry onto its image.-/
lemma inclusion_in_double_dual_isometry (x : E) : ∥inclusion_in_double_dual 𝕜 E x∥ = ∥x∥ :=
begin
  apply le_antisymm,
  { exact double_dual_bound 𝕜 E x },
  { rw continuous_linear_map.norm_def,
    apply real.lb_le_Inf _ continuous_linear_map.bounds_nonempty,
    rintros c ⟨hc1, hc2⟩,
    exact norm_le_dual_bound x hc1 hc2 },
end

end bidual_isometry

end normed_space
