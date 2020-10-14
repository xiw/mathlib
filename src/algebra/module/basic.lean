/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
import group_theory.group_action
import tactic.nth_rewrite
import algebra.group.hom

/-!
# Modules over a ring

In this file we define

* `semimodule R M` : an additive commutative monoid `M` is a `semimodule` over a
  `semiring` `R` if for `r : R` and `x : M` their "scalar multiplication `r • x : M` is defined, and
  the operation `•` satisfies some natural associativity and distributivity axioms similar to those
  on a ring.

* `module R M` : same as `semimodule R M` but assumes that `R` is a `ring` and `M` is an
  additive commutative group.

* `vector_space k M` : same as `semimodule k M` and `module k M` but assumes that `k` is a `field`
  and `M` is an additive commutative group.

* `linear_map R M M₂`, `M →ₗ[R] M₂` : a linear map between two R-`semimodule`s.

* `is_linear_map R f` : predicate saying that `f : M → M₂` is a linear map.

## Implementation notes

* `vector_space` and `module` are abbreviations for `semimodule R M`.

## Tags

semimodule, module, vector space, linear map
-/

open function
open_locale big_operators

universes u u' v w x y z
variables {R : Type u} {k : Type u'} {S : Type v} {M : Type w} {M₂ : Type x} {M₃ : Type y}
  {ι : Type z}

/-- A semimodule is a generalization of vector spaces to a scalar semiring.
  It consists of a scalar semiring `R` and an additive monoid of "vectors" `M`,
  connected by a "scalar multiplication" operation `r • x : M`
  (where `r : R` and `x : M`) with some natural associativity and
  distributivity axioms similar to those on a ring. -/
@[protect_proj] class semimodule (R : Type u) (M : Type v) [semiring R]
  [add_comm_monoid M] extends distrib_mul_action R M :=
(add_smul : ∀(r s : R) (x : M), (r + s) • x = r • x + s • x)
(zero_smul : ∀x : M, (0 : R) • x = 0)

section add_comm_monoid
variables [semiring R] [add_comm_monoid M] [semimodule R M] (r s : R) (x y : M)

theorem add_smul : (r + s) • x = r • x + s • x := semimodule.add_smul r s x
variables (R)
@[simp] theorem zero_smul : (0 : R) • x = 0 := semimodule.zero_smul x

theorem two_smul : (2 : R) • x = x + x := by rw [bit0, add_smul, one_smul]

/-- Pullback a `semimodule` structure along an injective additive monoid homomorphism. -/
protected def function.injective.semimodule [add_comm_monoid M₂] [has_scalar R M₂] (f : M₂ →+ M)
  (hf : injective f) (smul : ∀ (c : R) x, f (c • x) = c • f x) :
  semimodule R M₂ :=
{ smul := (•),
  add_smul := λ c₁ c₂ x, hf $ by simp only [smul, f.map_add, add_smul],
  zero_smul := λ x, hf $ by simp only [smul, zero_smul, f.map_zero],
  .. hf.distrib_mul_action f smul }

/-- Pushforward a `semimodule` structure along a surjective additive monoid homomorphism. -/
protected def function.surjective.semimodule [add_comm_monoid M₂] [has_scalar R M₂] (f : M →+ M₂)
  (hf : surjective f) (smul : ∀ (c : R) x, f (c • x) = c • f x) :
  semimodule R M₂ :=
{ smul := (•),
  add_smul := λ c₁ c₂ x, by { rcases hf x with ⟨x, rfl⟩,
    simp only [add_smul, ← smul, ← f.map_add] },
  zero_smul := λ x, by { rcases hf x with ⟨x, rfl⟩, simp only [← f.map_zero, ← smul, zero_smul] },
  .. hf.distrib_mul_action f smul }

variable (M)

/-- `(•)` as an `add_monoid_hom`. -/
def smul_add_hom : R →+ M →+ M :=
{ to_fun := const_smul_hom M,
  map_zero' := add_monoid_hom.ext $ λ r, by simp,
  map_add' := λ x y, add_monoid_hom.ext $ λ r, by simp [add_smul] }

variables {R M}

@[simp] lemma smul_add_hom_apply (r : R) (x : M) :
  smul_add_hom R M r x = r • x := rfl

lemma semimodule.eq_zero_of_zero_eq_one (zero_eq_one : (0 : R) = 1) : x = 0 :=
by rw [←one_smul R x, ←zero_eq_one, zero_smul]

lemma list.sum_smul {l : list R} {x : M} : l.sum • x = (l.map (λ r, r • x)).sum :=
((smul_add_hom R M).flip x).map_list_sum l

lemma multiset.sum_smul {l : multiset R} {x : M} : l.sum • x = (l.map (λ r, r • x)).sum :=
((smul_add_hom R M).flip x).map_multiset_sum l

lemma finset.sum_smul {f : ι → R} {s : finset ι} {x : M} :
  (∑ i in s, f i) • x = (∑ i in s, (f i) • x) :=
((smul_add_hom R M).flip x).map_sum f s

end add_comm_monoid

variables (R)

/-- An `add_comm_monoid` that is a `semimodule` over a `ring` carries a natural `add_comm_group` structure. -/
def semimodule.add_comm_monoid_to_add_comm_group [ring R] [add_comm_monoid M] [semimodule R M] :
  add_comm_group M :=
{ neg          := λ a, (-1 : R) • a,
  add_left_neg := λ a, by {
    nth_rewrite 1 ← one_smul _ a,
    rw [← add_smul, add_left_neg, zero_smul], },
  ..(infer_instance : add_comm_monoid M), }

variables {R}

section add_comm_group

variables (R M) [semiring R] [add_comm_group M]

/-- A structure containing most informations as in a semimodule, except the fields `zero_smul`
and `smul_zero`. As these fields can be deduced from the other ones when `M` is an `add_comm_group`,
this provides a way to construct a semimodule structure by checking less properties, in
`semimodule.of_core`. -/
@[nolint has_inhabited_instance]
structure semimodule.core extends has_scalar R M :=
(smul_add : ∀(r : R) (x y : M), r • (x + y) = r • x + r • y)
(add_smul : ∀(r s : R) (x : M), (r + s) • x = r • x + s • x)
(mul_smul : ∀(r s : R) (x : M), (r * s) • x = r • s • x)
(one_smul : ∀x : M, (1 : R) • x = x)

variables {R M}

/-- Define `semimodule` without proving `zero_smul` and `smul_zero` by using an auxiliary
structure `semimodule.core`, when the underlying space is an `add_comm_group`. -/
def semimodule.of_core (H : semimodule.core R M) : semimodule R M :=
by letI := H.to_has_scalar; exact
{ zero_smul := λ x, (add_monoid_hom.mk' (λ r : R, r • x) (λ r s, H.add_smul r s x)).map_zero,
  smul_zero := λ r, (add_monoid_hom.mk' ((•) r) (H.smul_add r)).map_zero,
  ..H }

end add_comm_group

/--
Modules are defined as an `abbreviation` for semimodules,
if the base semiring is a ring.
(A previous definition made `module` a structure
defined to be `semimodule`.)
This has as advantage that modules are completely transparent
for type class inference, which means that all instances for semimodules
are immediately picked up for modules as well.
A cosmetic disadvantage is that one can not extend modules as such,
in definitions such as `normed_space`.
The solution is to extend `semimodule` instead.
-/
library_note "module definition"

/-- A module is the same as a semimodule, except the scalar semiring is actually
  a ring.
  This is the traditional generalization of spaces like `ℤ^n`, which have a natural
  addition operation and a way to multiply them by elements of a ring, but no multiplication
  operation between vectors. -/
abbreviation module (R : Type u) (M : Type v) [ring R] [add_comm_group M] :=
semimodule R M

/--
To prove two module structures on a fixed `add_comm_group` agree,
it suffices to check the scalar multiplications agree.
-/
-- We'll later use this to show `module ℤ M` is a subsingleton.
@[ext]
lemma module_ext {R : Type*} [ring R] {M : Type*} [add_comm_group M] (P Q : module R M)
  (w : ∀ (r : R) (m : M), by { haveI := P, exact r • m } = by { haveI := Q, exact r • m }) :
  P = Q :=
begin
  unfreezingI { rcases P with ⟨⟨⟨⟨P⟩⟩⟩⟩, rcases Q with ⟨⟨⟨⟨Q⟩⟩⟩⟩ },
  congr,
  funext r m,
  exact w r m,
  all_goals { apply proof_irrel_heq },
end

section module
variables [ring R] [add_comm_group M] [module R M] (r s : R) (x y : M)

@[simp] theorem neg_smul : -r • x = - (r • x) :=
eq_neg_of_add_eq_zero (by rw [← add_smul, add_left_neg, zero_smul])

variables (R)
theorem neg_one_smul (x : M) : (-1 : R) • x = -x := by simp
variables {R}

theorem sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y :=
by simp [add_smul, sub_eq_add_neg]

theorem smul_eq_zero {R E : Type*} [division_ring R] [add_comm_group E] [module R E]
  {c : R} {x : E} :
  c • x = 0 ↔ c = 0 ∨ x = 0 :=
⟨λ h, or_iff_not_imp_left.2 $ λ hc, (units.mk0 c hc).smul_eq_zero.1 h,
  λ h, h.elim (λ hc, hc.symm ▸ zero_smul R x) (λ hx, hx.symm ▸ smul_zero c)⟩

end module

/-- A semimodule over a `subsingleton` semiring is a `subsingleton`. We cannot register this
as an instance because Lean has no way to guess `R`. -/
theorem semimodule.subsingleton (R M : Type*) [semiring R] [subsingleton R] [add_comm_monoid M]
  [semimodule R M] :
  subsingleton M :=
⟨λ x y, by rw [← one_smul R x, ← one_smul R y, subsingleton.elim (1:R) 0, zero_smul, zero_smul]⟩

@[priority 910] -- see Note [lower instance priority]
instance semiring.to_semimodule [semiring R] : semimodule R R :=
{ smul := (*),
  smul_add := mul_add,
  add_smul := add_mul,
  mul_smul := mul_assoc,
  one_smul := one_mul,
  zero_smul := zero_mul,
  smul_zero := mul_zero }

@[simp] lemma smul_eq_mul [semiring R] {a a' : R} : a • a' = a * a' := rfl

/-- A ring homomorphism `f : R →+* M` defines a module structure by `r • x = f r * x`. -/
def ring_hom.to_semimodule [semiring R] [semiring S] (f : R →+* S) : semimodule R S :=
{ smul := λ r x, f r * x,
  smul_add := λ r x y, by unfold has_scalar.smul; rw [mul_add],
  add_smul := λ r s x, by unfold has_scalar.smul; rw [f.map_add, add_mul],
  mul_smul := λ r s x, by unfold has_scalar.smul; rw [f.map_mul, mul_assoc],
  one_smul := λ x, show f 1 * x = _, by rw [f.map_one, one_mul],
  zero_smul := λ x, show f 0 * x = 0, by rw [f.map_zero, zero_mul],
  smul_zero := λ r, mul_zero (f r) }

/-- A map `f` between semimodules over a semiring is linear if it satisfies the two properties
`f (x + y) = f x + f y` and `f (c • x) = c • f x`. The predicate `is_linear_map R f` asserts this
property. A bundled version is available with `linear_map`, and should be favored over
`is_linear_map` most of the time. -/
structure is_linear_map (R : Type u) {M : Type v} {M₂ : Type w}
  [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂]
  (f : M → M₂) : Prop :=
(map_add : ∀ x y, f (x + y) = f x + f y)
(map_smul : ∀ (c : R) x, f (c • x) = c • f x)


set_option old_structure_cmd true

/-- A map `f` between semimodules over a semiring is linear if it satisfies the two properties
`f (x + y) = f x + f y` and `f (c • x) = c • f x`. Elements of `linear_map R M M₂` (available under
the notation `M →ₗ[R] M₂`) are bundled versions of such maps. An unbundled version is available with
the predicate `is_linear_map`, but it should be avoided most of the time. -/
structure linear_map (R : Type u) (M : Type v) (M₂ : Type w)
  [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂] extends add_hom M M₂ :=
(map_smul' : ∀(c : R) x, to_fun (c • x) = c • to_fun x)

/-- The `add_hom` underlying a `linear_map`. -/
add_decl_doc linear_map.to_add_hom

set_option old_structure_cmd false

infixr ` →ₗ `:25 := linear_map _
notation M ` →ₗ[`:25 R:25 `] `:0 M₂:0 := linear_map R M M₂

namespace linear_map

section add_comm_monoid

variables [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃]

section
variables [semimodule R M] [semimodule R M₂]

instance : has_coe_to_fun (M →ₗ[R] M₂) := ⟨_, to_fun⟩

@[simp] lemma coe_mk (f : M → M₂) (h₁ h₂) :
  ((linear_map.mk f h₁ h₂ : M →ₗ[R] M₂) : M → M₂) = f := rfl

/-- Identity map as a `linear_map` -/
def id : M →ₗ[R] M :=
⟨id, λ _ _, rfl, λ _ _, rfl⟩

lemma id_apply (x : M) :
  @id R M _ _ _ x = x := rfl

@[simp, norm_cast] lemma id_coe : ((linear_map.id : M →ₗ[R] M) : M → M) = _root_.id :=
by { ext x, refl }

end

section
-- We can infer the module structure implicitly from the linear maps,
-- rather than via typeclass resolution.
variables {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂}
variables (f g : M →ₗ[R] M₂)
include semimodule_M semimodule_M₂

@[simp] lemma to_fun_eq_coe : f.to_fun = ⇑f := rfl

theorem is_linear : is_linear_map R f := ⟨f.2, f.3⟩

variables {f g}

theorem coe_injective : injective (λ f : M →ₗ[R] M₂, show M → M₂, from f) :=
by rintro ⟨f, _⟩ ⟨g, _⟩ ⟨h⟩; congr

@[ext] theorem ext (H : ∀ x, f x = g x) : f = g :=
coe_injective $ funext H

lemma coe_fn_congr : Π {x x' : M}, x = x' → f x = f x'
| _ _ rfl := rfl

theorem ext_iff : f = g ↔ ∀ x, f x = g x :=
⟨by { rintro rfl x, refl } , ext⟩

/-- If two linear maps are equal, they are equal at each point. -/
lemma lcongr_fun (h : f = g) (m : M) : f m = g m :=
congr_fun (congr_arg linear_map.to_fun h) m

variables (f g)

@[simp] lemma map_add (x y : M) : f (x + y) = f x + f y := f.map_add' x y

@[simp] lemma map_smul (c : R) (x : M) : f (c • x) = c • f x := f.map_smul' c x

@[simp] lemma map_zero : f 0 = 0 :=
by rw [← zero_smul R, map_smul f 0 0, zero_smul]

instance : is_add_monoid_hom f :=
{ map_add := map_add f,
  map_zero := map_zero f }

/-- convert a linear map to an additive map -/
def to_add_monoid_hom : M →+ M₂ :=
{ to_fun := f,
  map_zero' := f.map_zero,
  map_add' := f.map_add }

@[simp] lemma to_add_monoid_hom_coe :
  ((f.to_add_monoid_hom) : M → M₂) = f := rfl

@[simp] lemma map_sum {ι} {t : finset ι} {g : ι → M} :
  f (∑ i in t, g i) = (∑ i in t, f (g i)) :=
f.to_add_monoid_hom.map_sum _ _

theorem to_add_monoid_hom_injective :
  function.injective (to_add_monoid_hom : (M →ₗ[R] M₂) → (M →+ M₂)) :=
λ f g h, ext $ add_monoid_hom.congr_fun h

end

section

variables {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂}
{semimodule_M₃ : semimodule R M₃}
variables (f : M₂ →ₗ[R] M₃) (g : M →ₗ[R] M₂)

/-- Composition of two linear maps is a linear map -/
def comp : M →ₗ[R] M₃ := ⟨f ∘ g, by simp, by simp⟩

@[simp] lemma comp_apply (x : M) : f.comp g x = f (g x) := rfl

@[norm_cast]
lemma comp_coe : (f : M₂ → M₃) ∘ (g : M → M₂) = f.comp g := rfl

end

end add_comm_monoid

section add_comm_group

variables [semiring R] [add_comm_group M] [add_comm_group M₂]
variables {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂}
variables (f : M →ₗ[R] M₂)

@[simp] lemma map_neg (x : M) : f (- x) = - f x :=
f.to_add_monoid_hom.map_neg x

@[simp] lemma map_sub (x y : M) : f (x - y) = f x - f y :=
f.to_add_monoid_hom.map_sub x y

instance : is_add_group_hom f :=
{ map_add := map_add f}

end add_comm_group

end linear_map

namespace is_linear_map

section add_comm_monoid
variables [semiring R] [add_comm_monoid M] [add_comm_monoid M₂]
variables [semimodule R M] [semimodule R M₂]
include R

/-- Convert an `is_linear_map` predicate to a `linear_map` -/
def mk' (f : M → M₂) (H : is_linear_map R f) : M →ₗ M₂ := ⟨f, H.1, H.2⟩

@[simp] theorem mk'_apply {f : M → M₂} (H : is_linear_map R f) (x : M) :
  mk' f H x = f x := rfl

lemma is_linear_map_smul {R M : Type*} [comm_semiring R] [add_comm_monoid M] [semimodule R M] (c : R) :
  is_linear_map R (λ (z : M), c • z) :=
begin
  refine is_linear_map.mk (smul_add c) _,
  intros _ _,
  simp only [smul_smul, mul_comm]
end

--TODO: move
lemma is_linear_map_smul' {R M : Type*} [semiring R] [add_comm_monoid M] [semimodule R M] (a : M) :
  is_linear_map R (λ (c : R), c • a) :=
is_linear_map.mk (λ x y, add_smul x y a) (λ x y, mul_smul x y a)

variables {f : M → M₂} (lin : is_linear_map R f)
include M M₂ lin

lemma map_zero : f (0 : M) = (0 : M₂) := (lin.mk' f).map_zero

end add_comm_monoid

section add_comm_group

variables [semiring R] [add_comm_group M] [add_comm_group M₂]
variables [semimodule R M] [semimodule R M₂]
include R

lemma is_linear_map_neg :
  is_linear_map R (λ (z : M), -z) :=
is_linear_map.mk neg_add (λ x y, (smul_neg x y).symm)

variables {f : M → M₂} (lin : is_linear_map R f)
include M M₂ lin

lemma map_neg (x : M) : f (- x) = - f x := (lin.mk' f).map_neg x

lemma map_sub (x y) : f (x - y) = f x - f y := (lin.mk' f).map_sub x y

end add_comm_group

end is_linear_map

/-- Ring of linear endomorphismsms of a module. -/
abbreviation module.End (R : Type u) (M : Type v)
  [semiring R] [add_comm_monoid M] [semimodule R M] := M →ₗ[R] M


/--
Vector spaces are defined as an `abbreviation` for semimodules,
if the base ring is a field.
(A previous definition made `vector_space` a structure
defined to be `module`.)
This has as advantage that vector spaces are completely transparent
for type class inference, which means that all instances for semimodules
are immediately picked up for vector spaces as well.
A cosmetic disadvantage is that one can not extend vector spaces as such,
in definitions such as `normed_space`.
The solution is to extend `semimodule` instead.
-/
library_note "vector space definition"

/-- A vector space is the same as a module, except the scalar ring is actually
  a field. (This adds commutativity of the multiplication and existence of inverses.)
  This is the traditional generalization of spaces like `ℝ^n`, which have a natural
  addition operation and a way to multiply them by real numbers, but no multiplication
  operation between vectors. -/
abbreviation vector_space (R : Type u) (M : Type v) [field R] [add_comm_group M] :=
semimodule R M

namespace add_comm_monoid
open add_monoid

variables [add_comm_monoid M]

/-- The natural ℕ-semimodule structure on any `add_comm_monoid`. -/
-- We don't make this a global instance, as it results in too many instances,
-- and confusing ambiguity in the notation `n • x` when `n : ℕ`.
def nat_semimodule : semimodule ℕ M :=
{ smul := nsmul,
  smul_add := λ _ _ _, nsmul_add _ _ _,
  add_smul := λ _ _ _, add_nsmul _ _ _,
  mul_smul := λ _ _ _, mul_nsmul _ _ _,
  one_smul := one_nsmul,
  zero_smul := zero_nsmul,
  smul_zero := nsmul_zero }

end add_comm_monoid

namespace add_comm_group

variables [add_comm_group M]

/-- The natural ℤ-module structure on any `add_comm_group`. -/
-- We don't immediately make this a global instance, as it results in too many instances,
-- and confusing ambiguity in the notation `n • x` when `n : ℤ`.
-- We do turn it into a global instance, but only at the end of this file,
-- and I remain dubious whether this is a good idea.
def int_module : module ℤ M :=
{ smul := gsmul,
  smul_add := λ _ _ _, gsmul_add _ _ _,
  add_smul := λ _ _ _, add_gsmul _ _ _,
  mul_smul := λ _ _ _, gsmul_mul _ _ _,
  one_smul := one_gsmul,
  zero_smul := zero_gsmul,
  smul_zero := gsmul_zero }

instance : subsingleton (module ℤ M) :=
begin
  split,
  intros P Q,
  ext,
  -- isn't that lovely: `r • m = r • m`
  have one_smul : by { haveI := P, exact (1 : ℤ) • m } = by { haveI := Q, exact (1 : ℤ) • m },
    begin
      rw [@one_smul ℤ _ _ (by { haveI := P, apply_instance, }) m],
      rw [@one_smul ℤ _ _ (by { haveI := Q, apply_instance, }) m],
    end,
  have nat_smul : ∀ n : ℕ, by { haveI := P, exact (n : ℤ) • m } = by { haveI := Q, exact (n : ℤ) • m },
    begin
      intro n,
      induction n with n ih,
      { erw [zero_smul, zero_smul], },
      { rw [int.coe_nat_succ, add_smul, add_smul],
        erw ih,
        rw [one_smul], }
    end,
  cases r,
  { rw [int.of_nat_eq_coe, nat_smul], },
  { rw [int.neg_succ_of_nat_coe, neg_smul, neg_smul, nat_smul], }
end

end add_comm_group

section
local attribute [instance] add_comm_monoid.nat_semimodule

lemma semimodule.smul_eq_smul (R : Type*) [semiring R]
  {M : Type*} [add_comm_monoid M] [semimodule R M]
  (n : ℕ) (b : M) : n • b = (n : R) • b :=
begin
  induction n with n ih,
  { rw [nat.cast_zero, zero_smul, zero_smul] },
  { change (n + 1) • b = (n + 1 : R) • b,
    rw [add_smul, add_smul, one_smul, ih, one_smul] }
end

lemma semimodule.nsmul_eq_smul (R : Type*) [semiring R]
  {M : Type*} [add_comm_monoid M] [semimodule R M] (n : ℕ) (b : M) :
  n •ℕ b = (n : R) • b :=
semimodule.smul_eq_smul R n b

lemma nat.smul_def {M : Type*} [add_comm_monoid M] (n : ℕ) (x : M) :
  n • x = n •ℕ x :=
rfl

end

section
local attribute [instance] add_comm_group.int_module

lemma gsmul_eq_smul {M : Type*} [add_comm_group M] (n : ℤ) (x : M) : gsmul n x = n • x := rfl

lemma module.gsmul_eq_smul_cast (R : Type*) [ring R] {M : Type*} [add_comm_group M] [module R M]
  (n : ℤ) (b : M) : gsmul n b = (n : R) • b :=
begin
  cases n,
  { apply semimodule.nsmul_eq_smul, },
  { dsimp,
    rw semimodule.nsmul_eq_smul R,
    push_cast,
    rw neg_smul, }
end

lemma module.gsmul_eq_smul {M : Type*} [add_comm_group M] [module ℤ M]
  (n : ℤ) (b : M) : gsmul n b = n • b :=
by rw [module.gsmul_eq_smul_cast ℤ, int.cast_id]

end

-- We prove this without using the `add_comm_group.int_module` instance, so the `•`s here
-- come from whatever the local `module ℤ` structure actually is.
lemma add_monoid_hom.map_int_module_smul
  [add_comm_group M] [add_comm_group M₂]
  [module ℤ M] [module ℤ M₂] (f : M →+ M₂) (x : ℤ) (a : M) : f (x • a) = x • f a :=
by simp only [← module.gsmul_eq_smul, f.map_gsmul]

lemma add_monoid_hom.map_int_cast_smul
  [ring R] [add_comm_group M] [add_comm_group M₂] [module R M] [module R M₂]
  (f : M →+ M₂) (x : ℤ) (a : M) : f ((x : R) • a) = (x : R) • f a :=
by simp only [← module.gsmul_eq_smul_cast, f.map_gsmul]

lemma add_monoid_hom.map_nat_cast_smul
  [semiring R] [add_comm_monoid M] [add_comm_monoid M₂]
  [semimodule R M] [semimodule R M₂] (f : M →+ M₂) (x : ℕ) (a : M) :
  f ((x : R) • a) = (x : R) • f a :=
by simp only [← semimodule.nsmul_eq_smul, f.map_nsmul]

lemma add_monoid_hom.map_rat_cast_smul {R : Type*} [division_ring R] [char_zero R]
  {E : Type*} [add_comm_group E] [module R E] {F : Type*} [add_comm_group F] [module R F]
  (f : E →+ F) (c : ℚ) (x : E) :
  f ((c : R) • x) = (c : R) • f x :=
begin
  have : ∀ (x : E) (n : ℕ), 0 < n → f (((n⁻¹ : ℚ) : R) • x) = ((n⁻¹ : ℚ) : R) • f x,
  { intros x n hn,
    replace hn : (n : R) ≠ 0 := nat.cast_ne_zero.2 (ne_of_gt hn),
    conv_rhs { congr, skip, rw [← one_smul R x, ← mul_inv_cancel hn, mul_smul] },
    rw [f.map_nat_cast_smul, smul_smul, rat.cast_inv, rat.cast_coe_nat,
      inv_mul_cancel hn, one_smul] },
  refine c.num_denom_cases_on (λ m n hn hmn, _),
  rw [rat.mk_eq_div, div_eq_mul_inv, rat.cast_mul, int.cast_coe_nat, mul_smul, mul_smul,
    rat.cast_coe_int, f.map_int_cast_smul, this _ n hn]
end

lemma add_monoid_hom.map_rat_module_smul {E : Type*} [add_comm_group E] [vector_space ℚ E]
  {F : Type*} [add_comm_group F] [module ℚ F] (f : E →+ F) (c : ℚ) (x : E) :
  f (c • x) = c • f x :=
rat.cast_id c ▸ f.map_rat_cast_smul c x

-- We finally turn on these instances globally:
attribute [instance] add_comm_monoid.nat_semimodule add_comm_group.int_module

/-- Reinterpret an additive homomorphism as a `ℤ`-linear map. -/
def add_monoid_hom.to_int_linear_map [add_comm_group M] [add_comm_group M₂] (f : M →+ M₂) :
  M →ₗ[ℤ] M₂ :=
⟨f, f.map_add, f.map_int_module_smul⟩

/-- Reinterpret an additive homomorphism as a `ℚ`-linear map. -/
def add_monoid_hom.to_rat_linear_map [add_comm_group M] [vector_space ℚ M]
  [add_comm_group M₂] [vector_space ℚ M₂] (f : M →+ M₂) :
  M →ₗ[ℚ] M₂ :=
⟨f, f.map_add, f.map_rat_module_smul⟩
