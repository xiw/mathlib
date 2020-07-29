/-
Copyright (c) 2020 Yury Kudryashov All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
import analysis.normed_space.operator_norm
import analysis.normed_space.extend
import analysis.convex.cone

/-!
# Hahn-Banach theorem

In this file we prove a version of Hahn-Banach theorem for continuous linear
functions on normed spaces over ℝ and ℂ.

We also prove a standard corollary, needed for the isometric inclusion in the double dual.

## TODO

Prove more corollaries

-/


class has_exists_extension_norm_eq (𝕜 : Type*)
  [nondiscrete_normed_field 𝕜] [normed_algebra ℝ 𝕜] : Prop :=
(exists_extension_norm_eq : ∀
  (E : Type*)
  [normed_group E] [normed_space 𝕜 E]
  (p : subspace 𝕜 E)
  (f : p →L[𝕜] 𝕜),
  ∃ g : E →L[𝕜] 𝕜, (∀ x : p, g x = f x) ∧ ∥g∥ = ∥f∥)

noncomputable def coe_from_ℝ (𝕜 : Type*)
[nondiscrete_normed_field 𝕜] [normed_algebra ℝ 𝕜] [has_exists_extension_norm_eq 𝕜]
  (x : ℝ) : 𝕜 :=
  x • (1 : 𝕜)

lemma norm_norm'
  (𝕜 : Type*) [nondiscrete_normed_field 𝕜] [normed_algebra ℝ 𝕜] [has_exists_extension_norm_eq 𝕜]
  (A : Type*) [normed_group A] [normed_space 𝕜 A]
  (x : A) : ∥(coe_from_ℝ 𝕜 ∥x∥)∥ = ∥x∥ := begin
  unfold coe_from_ℝ,
  rw [norm_smul, norm_norm, normed_field.norm_one, mul_one],
end



section basic
variables {E : Type*} [normed_group E] [normed_space ℝ E]

/-- Hahn-Banach theorem for continuous linear functions over ℝ. -/
theorem exists_extension_norm_eq (p : subspace ℝ E) (f : p →L[ℝ] ℝ) :
  ∃ g : E →L[ℝ] ℝ, (∀ x : p, g x = f x) ∧ ∥g∥ = ∥f∥ :=
begin
  rcases exists_extension_of_le_sublinear ⟨p, f⟩ (λ x, ∥f∥ * ∥x∥)
    (λ c hc x, by simp only [norm_smul c x, real.norm_eq_abs, abs_of_pos hc, mul_left_comm])
    (λ x y, _) (λ x, le_trans (le_abs_self _) (f.le_op_norm _))
    with ⟨g, g_eq, g_le⟩,
  set g' := g.mk_continuous (∥f∥)
    (λ x, abs_le.2 ⟨neg_le.1 $ g.map_neg x ▸ norm_neg x ▸ g_le (-x), g_le x⟩),
  { refine ⟨g', g_eq, _⟩,
    { apply le_antisymm (g.mk_continuous_norm_le (norm_nonneg f) _),
      refine f.op_norm_le_bound (norm_nonneg _) (λ x, _),
      dsimp at g_eq,
      rw ← g_eq,
      apply g'.le_op_norm } },
  { simp only [← mul_add],
    exact mul_le_mul_of_nonneg_left (norm_add_le x y) (norm_nonneg f) }
end

noncomputable instance real_has_exists_extension_norm_eq : has_exists_extension_norm_eq ℝ :=
⟨by { intros, apply exists_extension_norm_eq }⟩

end basic

section complex
variables {F : Type*} [normed_group F] [normed_space ℂ F]

-- Inlining the following two definitions causes a type mismatch between
-- subspace ℝ (module.restrict_scalars ℝ ℂ F) and subspace ℂ F.
/-- Restrict a ℂ-subspace to an ℝ-subspace. -/
noncomputable def restrict_scalars (p: subspace ℂ F) : subspace ℝ F := p.restrict_scalars ℝ ℂ F

private lemma apply_real (p : subspace ℂ F) (f' : p →L[ℝ] ℝ) :
  ∃ g : F →L[ℝ] ℝ, (∀ x : restrict_scalars p, g x = f' x) ∧ ∥g∥ = ∥f'∥ :=
  exists_extension_norm_eq (p.restrict_scalars ℝ ℂ F) f'

open complex

/-- Hahn-Banach theorem for continuous linear functions over ℂ. -/
theorem complex.exists_extension_norm_eq (p : subspace ℂ F) (f : p →L[ℂ] ℂ) :
  ∃ g : F →L[ℂ] ℂ, (∀ x : p, g x = f x) ∧ ∥g∥ = ∥f∥ :=
begin
  -- Let `fr: p →L[ℝ] ℝ` be the real part of `f`.
  let fr := continuous_linear_map.re.comp (f.restrict_scalars ℝ),
  have fr_apply : ∀ x, fr x = (f x).re := λ x, rfl,

  -- Use the real version to get a norm-preserving extension of `fr`, which we'll call `g: F →L[ℝ] ℝ`.
  rcases apply_real p fr with ⟨g, ⟨hextends, hnormeq⟩⟩,

  -- Now `g` can be extended to the `F →L[ℂ] ℂ` we need.
  use g.extend_to_ℂ,

  -- It is an extension of `f`.
  have h : ∀ x : p, g.extend_to_ℂ x = f x,
  { intros,
    change (⟨g x, -g ((I • x) : p)⟩ : ℂ) = f x,
    ext; dsimp only; rw [hextends, fr_apply],
    rw [continuous_linear_map.map_smul, algebra.id.smul_eq_mul, mul_re, I_re, I_im],
    ring },

  refine ⟨h, _⟩,

  -- And we derive the equality of the norms by bounding on both sides.
  refine le_antisymm _ _,
  { calc ∥g.extend_to_ℂ∥
        ≤ ∥g∥ : g.extend_to_ℂ.op_norm_le_bound g.op_norm_nonneg (norm_bound _)
    ... = ∥fr∥ : hnormeq
    ... ≤ ∥continuous_linear_map.re∥ * ∥f∥ : continuous_linear_map.op_norm_comp_le _ _
    ... = ∥f∥ : by rw [complex.continuous_linear_map.re_norm, one_mul] },

  { exact f.op_norm_le_bound g.extend_to_ℂ.op_norm_nonneg (λ x, h x ▸ g.extend_to_ℂ.le_op_norm x) },
end

noncomputable instance complex_has_exists_extension_norm_eq : has_exists_extension_norm_eq ℂ :=
⟨by { intros, apply complex.exists_extension_norm_eq }⟩

end complex

section dual_vector
variables {E : Type*} [normed_group E] [normed_space ℝ E]

open continuous_linear_equiv
open_locale classical

lemma coord_self' (x : E) (h : x ≠ 0) : (∥x∥ • (coord ℝ x h))
  ⟨x, submodule.mem_span_singleton_self x⟩ = ∥x∥ :=
calc (∥x∥ • (coord ℝ x h)) ⟨x, submodule.mem_span_singleton_self x⟩
    = ∥x∥ • (linear_equiv.coord ℝ E x h) ⟨x, submodule.mem_span_singleton_self x⟩ : rfl
... = ∥x∥ • 1 : by rw linear_equiv.coord_self ℝ E x h
... = ∥x∥ : mul_one _

lemma coord_norm' (x : E) (h : x ≠ 0) : ∥∥x∥ • coord ℝ x h∥ = 1 :=
by rw [norm_smul, norm_norm, coord_norm, mul_inv_cancel (mt norm_eq_zero.mp h)]

/-- Corollary of Hahn-Banach.  Given a nonzero element `x` of a normed space, there exists an
    element of the dual space, of norm 1, whose value on `x` is `∥x∥`. -/
theorem exists_dual_vector (x : E) (h : x ≠ 0) : ∃ g : E →L[ℝ] ℝ, ∥g∥ = 1 ∧ g x = ∥x∥ :=
begin
  cases exists_extension_norm_eq (submodule.span ℝ {x}) (∥x∥ • coord ℝ x h) with g hg,
  use g, split,
  { rw [hg.2, coord_norm'] },
  { calc g x = g (⟨x, submodule.mem_span_singleton_self x⟩ : submodule.span ℝ {x}) : by simp
  ... = (∥x∥ • coord ℝ x h) (⟨x, submodule.mem_span_singleton_self x⟩ : submodule.span ℝ {x}) : by rw ← hg.1
  ... = ∥x∥ : by rw coord_self' }
end

/-- Variant of the above theorem, eliminating the hypothesis that `x` be nonzero, and choosing
    the dual element arbitrarily when `x = 0`. -/
theorem exists_dual_vector' [nontrivial E] (x : E) : ∃ g : E →L[ℝ] ℝ,
  ∥g∥ = 1 ∧ g x = ∥x∥ :=
begin
  by_cases hx : x = 0,
  { rcases exists_ne (0 : E) with ⟨y, hy⟩,
    cases exists_dual_vector y hy with g hg,
    use g, refine ⟨hg.left, _⟩, simp [hx] },
  { exact exists_dual_vector x hx }
end

end dual_vector

namespace complex

variables {E : Type*} [normed_group E] [normed_space ℂ  E]

open continuous_linear_equiv
open_locale classical

lemma coord_self' (x : E) (h : x ≠ 0) : (∥x∥ • (coord ℂ x h))
  ⟨x, submodule.mem_span_singleton_self x⟩ = ∥x∥ :=
calc (∥x∥ • (coord ℂ x h)) ⟨x, submodule.mem_span_singleton_self x⟩
    = ∥x∥ • (linear_equiv.coord ℂ E x h) ⟨x, submodule.mem_span_singleton_self x⟩ : rfl
... = ∥x∥ • 1 : by rw linear_equiv.coord_self ℂ E x h
... = ∥x∥ : mul_one _

lemma coord_norm' (x : E) (h : x ≠ 0) : ∥∥x∥ • coord ℂ x h∥ = 1 :=
by rw [norm_smul, norm_norm, coord_norm, mul_inv_cancel (mt norm_eq_zero.mp h)]

/-- Corollary of Hahn-Banach.  Given a nonzero element `x` of a normed space, there exists an
    element of the dual space, of norm 1, whose value on `x` is `∥x∥`. -/
theorem exists_dual_vector (x : E) (h : x ≠ 0) : ∃ g : E →L[ℂ] ℂ, ∥g∥ = 1 ∧ g x = ∥x∥ :=
begin
  cases complex.exists_extension_norm_eq (submodule.span ℂ {x}) (∥x∥ • coord ℂ x h) with g hg,
  use g, split,
  { rw [hg.2, coord_norm'] },
  { calc g x = g (⟨x, submodule.mem_span_singleton_self x⟩ : submodule.span ℂ {x}) : by simp
  ... = (∥x∥ • coord ℂ x h) (⟨x, submodule.mem_span_singleton_self x⟩ : submodule.span ℂ {x}) : by rw ← hg.1
  ... = ∥x∥ : by rw coord_self' }
end

/-- Variant of the above theorem, eliminating the hypothesis that `x` be nonzero, and choosing
    the dual element arbitrarily when `x = 0`. -/
theorem exists_dual_vector' [nontrivial E] (x : E) : ∃ g : E →L[ℂ] ℂ,
  ∥g∥ = 1 ∧ g x = ∥x∥ :=
begin
  by_cases hx : x = 0,
  { rcases exists_ne (0 : E) with ⟨y, hy⟩,
    cases exists_dual_vector y hy with g hg,
    use g, refine ⟨hg.left, _⟩, simp [hx] },
  { exact exists_dual_vector x hx }
end

end complex
