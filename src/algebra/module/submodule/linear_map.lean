import algebra.module.submodule.basic

/-!
# Linear maps and submodules
-/

variables {R M M₂ M₃ M₄ : Type*}

namespace linear_map

section add_comm_monoid
variables [semiring R]
variables [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [add_comm_monoid M₄]
variables [semimodule R M] [semimodule R M₂] [semimodule R M₃] [semimodule R M₄]
variables (f g : M →ₗ[R] M₂)
include R

/-- The restriction of a linear map `f : M → M₂` to a submodule `p ⊆ M` gives a linear map
`p → M₂`. -/
def dom_restrict (f : M →ₗ[R] M₂) (p : submodule R M) : p →ₗ[R] M₂ := f.comp p.subtype

@[simp] lemma dom_restrict_apply (f : M →ₗ[R] M₂) (p : submodule R M) (x : p) :
  f.dom_restrict p x = f x := rfl

/-- A linear map `f : M₂ → M` whose values lie in a submodule `p ⊆ M` can be restricted to a
linear map M₂ → p. -/
def cod_restrict (p : submodule R M) (f : M₂ →ₗ[R] M) (h : ∀c, f c ∈ p) : M₂ →ₗ[R] p :=
by refine {to_fun := λc, ⟨f c, h c⟩, ..}; intros; apply set_coe.ext; simp

@[simp] theorem cod_restrict_apply (p : submodule R M) (f : M₂ →ₗ[R] M) {h} (x : M₂) :
  (cod_restrict p f h x : M) = f x := rfl

@[simp] lemma comp_cod_restrict (p : submodule R M₂) (h : ∀b, f b ∈ p) (g : M₃ →ₗ[R] M) :
  (cod_restrict p f h).comp g = cod_restrict p (f.comp g) (assume b, h _) :=
ext $ assume b, rfl

@[simp] lemma subtype_comp_cod_restrict (p : submodule R M₂) (h : ∀b, f b ∈ p) :
  p.subtype.comp (cod_restrict p f h) = f :=
ext $ assume b, rfl

/-- Restrict domain and codomain of an endomorphism. -/
def restrict (f : M →ₗ[R] M) {p : submodule R M} (hf : ∀ x ∈ p, f x ∈ p) : p →ₗ[R] p :=
{ to_fun := λ x, ⟨f x, hf x.1 x.2⟩,
  map_add' := begin intros, apply set_coe.ext, simp end,
  map_smul' := begin intros, apply set_coe.ext, simp end }

lemma restrict_apply
  {f : M →ₗ[R] M} {p : submodule R M} (hf : ∀ x ∈ p, f x ∈ p) (x : p) :
  f.restrict hf x = ⟨f x, hf x.1 x.2⟩ := rfl

lemma subtype_comp_restrict {f : M →ₗ[R] M} {p : submodule R M} (hf : ∀ x ∈ p, f x ∈ p) :
  p.subtype.comp (f.restrict hf) = f.dom_restrict p := rfl

lemma restrict_eq_cod_restrict_dom_restrict
  {f : M →ₗ[R] M} {p : submodule R M} (hf : ∀ x ∈ p, f x ∈ p) :
  f.restrict hf = (f.dom_restrict p).cod_restrict p (λ x, hf x.1 x.2) := rfl

lemma restrict_eq_dom_restrict_cod_restrict
  {f : M →ₗ[R] M} {p : submodule R M} (hf : ∀ x, f x ∈ p) :
  f.restrict (λ x _, hf x) = (f.cod_restrict p hf).dom_restrict p := rfl

end add_comm_monoid

end linear_map

namespace submodule

section add_comm_monoid

variables [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃]
variables [semimodule R M] [semimodule R M₂] [semimodule R M₃]
variables (p p' : submodule R M) (q q' : submodule R M₂)
variables {r : R} {x y : M}
open set

/-- The pushforward of a submodule `p ⊆ M` by `f : M → M₂` -/
def map (f : M →ₗ[R] M₂) (p : submodule R M) : submodule R M₂ :=
{ carrier   := f '' p,
  smul_mem' := by rintro a _ ⟨b, hb, rfl⟩; exact ⟨_, p.smul_mem _ hb, f.map_smul _ _⟩,
  .. p.to_add_submonoid.map f.to_add_monoid_hom }

@[simp] lemma map_coe (f : M →ₗ[R] M₂) (p : submodule R M) :
  (map f p : set M₂) = f '' p := rfl

@[simp] lemma mem_map {f : M →ₗ[R] M₂} {p : submodule R M} {x : M₂} :
  x ∈ map f p ↔ ∃ y, y ∈ p ∧ f y = x := iff.rfl

theorem mem_map_of_mem {f : M →ₗ[R] M₂} {p : submodule R M} {r} (h : r ∈ p) : f r ∈ map f p :=
set.mem_image_of_mem _ h

lemma map_id : map linear_map.id p = p :=
submodule.ext $ λ a, by simp

lemma map_comp (f : M →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (p : submodule R M) :
  map (g.comp f) p = map g (map f p) :=
submodule.coe_injective $ by simp [map_coe]; rw ← image_comp

/-- The pullback of a submodule `p ⊆ M₂` along `f : M → M₂` -/
def comap (f : M →ₗ[R] M₂) (p : submodule R M₂) : submodule R M :=
{ carrier   := f ⁻¹' p,
  smul_mem' := λ a x h, by simp [p.smul_mem _ h],
  .. p.to_add_submonoid.comap f.to_add_monoid_hom }

@[simp] lemma comap_coe (f : M →ₗ[R] M₂) (p : submodule R M₂) :
  (comap f p : set M) = f ⁻¹' p := rfl

@[simp] lemma mem_comap {f : M →ₗ[R] M₂} {p : submodule R M₂} :
  x ∈ comap f p ↔ f x ∈ p := iff.rfl

lemma comap_id : comap linear_map.id p = p :=
submodule.coe_injective rfl

lemma comap_comp (f : M →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (p : submodule R M₃) :
  comap (g.comp f) p = comap f (comap g p) := rfl

end add_comm_monoid

end submodule
