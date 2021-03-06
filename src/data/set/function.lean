/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Andrew Zipperer, Haitao Zhang, Minchao Wu, Yury Kudryashov
-/
import data.set.basic
import logic.function.conjugate

/-!
# Functions over sets

## Main definitions

### Predicate

* `eq_on f₁ f₂ s` : functions `f₁` and `f₂` are equal at every point of `s`;
* `maps_to f s t` : `f` sends every point of `s` to a point of `t`;
* `inj_on f s` : restriction of `f` to `s` is injective;
* `surj_on f s t` : every point in `s` has a preimage in `s`;
* `bij_on f s t` : `f` is a bijection between `s` and `t`;
* `left_inv_on f' f s` : for every `x ∈ s` we have `f' (f x) = x`;
* `right_inv_on f' f t` : for every `y ∈ t` we have `f (f' y) = y`;
* `inv_on f' f s t` : `f'` is a two-side inverse of `f` on `s` and `t`, i.e.
  we have `left_inv_on f' f s` and `right_inv_on f' f t`.

### Functions

* `restrict f s` : restrict the domain of `f` to the set `s`;
* `cod_restrict f s h` : given `h : ∀ x, f x ∈ s`, restrict the codomain of `f` to the set `s`;
* `maps_to.restrict f s t h`: given `h : maps_to f s t`, restrict the domain of `f` to `s`
  and the codomain to `t`.
-/
universes u v w x y

variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

open function

namespace set

/-! ### Restrict -/

/-- Restrict domain of a function `f` to a set `s`. Same as `subtype.restrict` but this version
takes an argument `↥s` instead of `subtype s`. -/
def restrict (f : α → β) (s : set α) : s → β := λ x, f x

lemma restrict_eq (f : α → β) (s : set α) : s.restrict f = f ∘ coe := rfl

@[simp] lemma restrict_apply (f : α → β) (s : set α) (x : s) : restrict f s x = f x := rfl

@[simp] lemma range_restrict (f : α → β) (s : set α) : set.range (restrict f s) = f '' s :=
(range_comp _ _).trans $ congr_arg (('') f) subtype.range_coe

/-- Restrict codomain of a function `f` to a set `s`. Same as `subtype.coind` but this version
has codomain `↥s` instead of `subtype s`. -/
def cod_restrict (f : α → β) (s : set β) (h : ∀ x, f x ∈ s) : α → s :=
λ x, ⟨f x, h x⟩

@[simp] lemma coe_cod_restrict_apply (f : α → β) (s : set β) (h : ∀ x, f x ∈ s) (x : α) :
  (cod_restrict f s h x : β) = f x :=
rfl

variables {s s₁ s₂ : set α} {t t₁ t₂ : set β} {p : set γ} {f f₁ f₂ f₃ : α → β} {g : β → γ}
  {f' f₁' f₂' : β → α} {g' : γ → β}

/-! ### Equality on a set -/

/-- Two functions `f₁ f₂ : α → β` are equal on `s`
  if `f₁ x = f₂ x` for all `x ∈ a`. -/
@[reducible] def eq_on (f₁ f₂ : α → β) (s : set α) : Prop :=
∀ ⦃x⦄, x ∈ s → f₁ x = f₂ x

@[symm] lemma eq_on.symm (h : eq_on f₁ f₂ s) : eq_on f₂ f₁ s :=
λ x hx, (h hx).symm

lemma eq_on_comm : eq_on f₁ f₂ s ↔ eq_on f₂ f₁ s :=
⟨eq_on.symm, eq_on.symm⟩

@[refl] lemma eq_on_refl (f : α → β) (s : set α) : eq_on f f s :=
λ _ _, rfl

@[trans] lemma eq_on.trans (h₁ : eq_on f₁ f₂ s) (h₂ : eq_on f₂ f₃ s) : eq_on f₁ f₃ s :=
λ x hx, (h₁ hx).trans (h₂ hx)

theorem eq_on.image_eq (heq : eq_on f₁ f₂ s) : f₁ '' s = f₂ '' s :=
image_congr heq

lemma eq_on.mono (hs : s₁ ⊆ s₂) (hf : eq_on f₁ f₂ s₂) : eq_on f₁ f₂ s₁ :=
λ x hx, hf (hs hx)

lemma comp_eq_of_eq_on_range {ι : Sort*} {f : ι → α} {g₁ g₂ : α → β} (h : eq_on g₁ g₂ (range f)) :
  g₁ ∘ f = g₂ ∘ f :=
funext $ λ x, h $ mem_range_self _

/-! ### maps to -/

/-- `maps_to f a b` means that the image of `a` is contained in `b`. -/
@[reducible] def maps_to (f : α → β) (s : set α) (t : set β) : Prop := ∀ ⦃x⦄, x ∈ s → f x ∈ t

/-- Given a map `f` sending `s : set α` into `t : set β`, restrict domain of `f` to `s`
and the codomain to `t`. Same as `subtype.map`. -/
def maps_to.restrict (f : α → β) (s : set α) (t : set β) (h : maps_to f s t) :
  s → t :=
subtype.map f h

@[simp] lemma maps_to.coe_restrict_apply (h : maps_to f s t) (x : s) :
  (h.restrict f s t x : β) = f x := rfl

lemma maps_to_iff_exists_map_subtype : maps_to f s t ↔ ∃ g : s → t, ∀ x : s, f x = g x :=
⟨λ h, ⟨h.restrict f s t, λ _, rfl⟩,
  λ ⟨g, hg⟩ x hx, by { erw [hg ⟨x, hx⟩], apply subtype.coe_prop }⟩

theorem maps_to' : maps_to f s t ↔ f '' s ⊆ t :=
image_subset_iff.symm

theorem maps_to_empty (f : α → β) (t : set β) : maps_to f ∅ t := empty_subset _

theorem maps_to.image_subset (h : maps_to f s t) : f '' s ⊆ t :=
maps_to'.1 h

theorem maps_to.congr (h₁ : maps_to f₁ s t) (h : eq_on f₁ f₂ s) :
  maps_to f₂ s t :=
λ x hx, h hx ▸ h₁ hx

theorem eq_on.maps_to_iff (H : eq_on f₁ f₂ s) : maps_to f₁ s t ↔ maps_to f₂ s t :=
⟨λ h, h.congr H, λ h, h.congr H.symm⟩

theorem maps_to.comp (h₁ : maps_to g t p) (h₂ : maps_to f s t) : maps_to (g ∘ f) s p :=
λ x h, h₁ (h₂ h)

theorem maps_to.iterate {f : α → α} {s : set α} (h : maps_to f s s) :
  ∀ n, maps_to (f^[n]) s s
| 0 := λ _, id
| (n+1) := (maps_to.iterate n).comp h

theorem maps_to.iterate_restrict {f : α → α} {s : set α} (h : maps_to f s s) (n : ℕ) :
  (h.restrict f s s^[n]) = (h.iterate n).restrict _ _ _ :=
begin
  funext x,
  rw [subtype.ext_iff, maps_to.coe_restrict_apply],
  induction n with n ihn generalizing x,
  { refl },
  { simp [nat.iterate, ihn] }
end

theorem maps_to.mono (hs : s₂ ⊆ s₁) (ht : t₁ ⊆ t₂) (hf : maps_to f s₁ t₁) :
  maps_to f s₂ t₂ :=
λ x hx, ht (hf $ hs hx)

theorem maps_to.union_union (h₁ : maps_to f s₁ t₁) (h₂ : maps_to f s₂ t₂) :
  maps_to f (s₁ ∪ s₂) (t₁ ∪ t₂) :=
λ x hx, hx.elim (λ hx, or.inl $ h₁ hx) (λ hx, or.inr $ h₂ hx)

theorem maps_to.union (h₁ : maps_to f s₁ t) (h₂ : maps_to f s₂ t) :
  maps_to f (s₁ ∪ s₂) t :=
union_self t ▸ h₁.union_union h₂

@[simp] theorem maps_to_union : maps_to f (s₁ ∪ s₂) t ↔ maps_to f s₁ t ∧ maps_to f s₂ t :=
⟨λ h, ⟨h.mono (subset_union_left s₁ s₂) (subset.refl t),
  h.mono (subset_union_right s₁ s₂) (subset.refl t)⟩, λ h, h.1.union h.2⟩

theorem maps_to.inter (h₁ : maps_to f s t₁) (h₂ : maps_to f s t₂) :
  maps_to f s (t₁ ∩ t₂) :=
λ x hx, ⟨h₁ hx, h₂ hx⟩

theorem maps_to.inter_inter (h₁ : maps_to f s₁ t₁) (h₂ : maps_to f s₂ t₂) :
  maps_to f (s₁ ∩ s₂) (t₁ ∩ t₂) :=
λ x hx, ⟨h₁ hx.1, h₂ hx.2⟩

@[simp] theorem maps_to_inter : maps_to f s (t₁ ∩ t₂) ↔ maps_to f s t₁ ∧ maps_to f s t₂ :=
⟨λ h, ⟨h.mono (subset.refl s) (inter_subset_left t₁ t₂),
  h.mono (subset.refl s) (inter_subset_right t₁ t₂)⟩, λ h, h.1.inter h.2⟩

theorem maps_to_univ (f : α → β) (s : set α) : maps_to f s univ := λ x h, trivial

theorem maps_to_image (f : α → β) (s : set α) : maps_to f s (f '' s) := by rw maps_to'

theorem maps_to_preimage (f : α → β) (t : set β) : maps_to f (f ⁻¹' t) t := subset.refl _

theorem maps_to_range (f : α → β) (s : set α) : maps_to f s (range f) :=
(maps_to_image f s).mono (subset.refl s) (image_subset_range _ _)

theorem surjective_maps_to_image_restrict (f : α → β) (s : set α) :
  surjective ((maps_to_image f s).restrict f s (f '' s)) :=
λ ⟨y, x, hs, hxy⟩, ⟨⟨x, hs⟩, subtype.ext hxy⟩

theorem maps_to.mem_iff (h : maps_to f s t) (hc : maps_to f sᶜ tᶜ) {x} : f x ∈ t ↔ x ∈ s :=
⟨λ ht, by_contra $ λ hs, hc hs ht, λ hx, h hx⟩

/-! ### Injectivity on a set -/

/-- `f` is injective on `a` if the restriction of `f` to `a` is injective. -/
@[reducible] def inj_on (f : α → β) (s : set α) : Prop :=
∀ ⦃x₁ : α⦄, x₁ ∈ s → ∀ ⦃x₂ : α⦄, x₂ ∈ s → f x₁ = f x₂ → x₁ = x₂

theorem inj_on_empty (f : α → β) : inj_on f ∅ :=
λ _ h₁, false.elim h₁

theorem inj_on.congr (h₁ : inj_on f₁ s) (h : eq_on f₁ f₂ s) :
  inj_on f₂ s :=
λ x hx y hy, h hx ▸ h hy ▸ h₁ hx hy

theorem eq_on.inj_on_iff (H : eq_on f₁ f₂ s) : inj_on f₁ s ↔ inj_on f₂ s :=
⟨λ h, h.congr H, λ h, h.congr H.symm⟩

theorem inj_on.mono (h : s₁ ⊆ s₂) (ht : inj_on f s₂) : inj_on f s₁ :=
λ x hx y hy H, ht (h hx) (h hy) H

theorem inj_on_insert {f : α → β} {s : set α} {a : α} (has : a ∉ s) :
  set.inj_on f (insert a s) ↔ set.inj_on f s ∧ f a ∉ f '' s :=
⟨λ hf, ⟨hf.mono $ subset_insert a s,
  λ ⟨x, hxs, hx⟩, has $ mem_of_eq_of_mem (hf (or.inl rfl) (or.inr hxs) hx.symm) hxs⟩,
λ ⟨h1, h2⟩ x hx y hy hfxy, or.cases_on hx
  (λ hxa : x = a, or.cases_on hy
    (λ hya : y = a, hxa.trans hya.symm)
    (λ hys : y ∈ s, h2.elim ⟨y, hys, hxa ▸ hfxy.symm⟩))
  (λ hxs : x ∈ s, or.cases_on hy
    (λ hya : y = a, h2.elim ⟨x, hxs, hya ▸ hfxy⟩)
    (λ hys : y ∈ s, h1 hxs hys hfxy))⟩

lemma injective_iff_inj_on_univ : injective f ↔ inj_on f univ :=
⟨λ h x hx y hy hxy, h hxy, λ h _ _ heq, h trivial trivial heq⟩

lemma inj_on_of_injective (h : injective f) (s : set α) : inj_on f s :=
λ x hx y hy hxy, h hxy

alias inj_on_of_injective ← function.injective.inj_on

theorem inj_on.comp (hg : inj_on g t) (hf: inj_on f s) (h : maps_to f s t) :
  inj_on (g ∘ f) s :=
λ x hx y hy heq, hf hx hy $ hg (h hx) (h hy) heq

lemma inj_on_iff_injective : inj_on f s ↔ injective (restrict f s) :=
⟨λ H a b h, subtype.eq $ H a.2 b.2 h,
 λ H a as b bs h, congr_arg subtype.val $ @H ⟨a, as⟩ ⟨b, bs⟩ h⟩

lemma inj_on.inv_fun_on_image [nonempty α] (h : inj_on f s₂) (ht : s₁ ⊆ s₂) :
  (inv_fun_on f s₂) '' (f '' s₁) = s₁ :=
begin
  have : eq_on ((inv_fun_on f s₂) ∘ f) id s₁, from λz hz, inv_fun_on_eq' h (ht hz),
  rw [← image_comp, this.image_eq, image_id]
end

lemma inj_on_preimage {B : set (set β)} (hB : B ⊆ powerset (range f)) :
  inj_on (preimage f) B :=
λ s hs t ht hst, (preimage_eq_preimage' (hB hs) (hB ht)).1 hst

/-! ### Surjectivity on a set -/

/-- `f` is surjective from `a` to `b` if `b` is contained in the image of `a`. -/
@[reducible] def surj_on (f : α → β) (s : set α) (t : set β) : Prop := t ⊆ f '' s

theorem surj_on.subset_range (h : surj_on f s t) : t ⊆ range f :=
subset.trans h $ image_subset_range f s

lemma surj_on_iff_exists_map_subtype :
  surj_on f s t ↔ ∃ (t' : set β) (g : s → t'), t ⊆ t' ∧ surjective g ∧ ∀ x : s, f x = g x :=
⟨λ h, ⟨_, (maps_to_image f s).restrict f s _, h, surjective_maps_to_image_restrict _ _, λ _, rfl⟩,
  λ ⟨t', g, htt', hg, hfg⟩ y hy, let ⟨x, hx⟩ := hg ⟨y, htt' hy⟩ in
    ⟨x, x.2, by rw [hfg, hx, subtype.coe_mk]⟩⟩

theorem surj_on_empty (f : α → β) (s : set α) : surj_on f s ∅ := empty_subset _

theorem surj_on.comap_nonempty (h : surj_on f s t) (ht : t.nonempty) : s.nonempty :=
(ht.mono h).of_image

theorem surj_on.congr (h : surj_on f₁ s t) (H : eq_on f₁ f₂ s) : surj_on f₂ s t :=
by rwa [surj_on, ← H.image_eq]

theorem eq_on.surj_on_iff (h : eq_on f₁ f₂ s) : surj_on f₁ s t ↔ surj_on f₂ s t :=
⟨λ H, H.congr h, λ H, H.congr h.symm⟩

theorem surj_on.mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) (hf : surj_on f s₁ t₂) : surj_on f s₂ t₁ :=
subset.trans ht $ subset.trans hf $ image_subset _ hs

theorem surj_on.union (h₁ : surj_on f s t₁) (h₂ : surj_on f s t₂) : surj_on f s (t₁ ∪ t₂) :=
λ x hx, hx.elim (λ hx, h₁ hx) (λ hx, h₂ hx)

theorem surj_on.union_union (h₁ : surj_on f s₁ t₁) (h₂ : surj_on f s₂ t₂) :
  surj_on f (s₁ ∪ s₂) (t₁ ∪ t₂) :=
(h₁.mono (subset_union_left _ _) (subset.refl _)).union
  (h₂.mono (subset_union_right _ _) (subset.refl _))

theorem surj_on.inter_inter (h₁ : surj_on f s₁ t₁) (h₂ : surj_on f s₂ t₂) (h : inj_on f (s₁ ∪ s₂)) :
  surj_on f (s₁ ∩ s₂) (t₁ ∩ t₂) :=
begin
  intros y hy,
  rcases h₁ hy.1 with ⟨x₁, hx₁, rfl⟩,
  rcases h₂ hy.2 with ⟨x₂, hx₂, heq⟩,
  have : x₁ = x₂, from h (or.inl hx₁) (or.inr hx₂) heq.symm,
  subst x₂,
  exact mem_image_of_mem f ⟨hx₁, hx₂⟩
end

theorem surj_on.inter (h₁ : surj_on f s₁ t) (h₂ : surj_on f s₂ t) (h : inj_on f (s₁ ∪ s₂)) :
  surj_on f (s₁ ∩ s₂) t :=
inter_self t ▸ h₁.inter_inter h₂ h

theorem surj_on.comp (hg : surj_on g t p) (hf : surj_on f s t) : surj_on (g ∘ f) s p :=
subset.trans hg $ subset.trans (image_subset g hf) $ (image_comp g f s) ▸ subset.refl _

lemma surjective_iff_surj_on_univ : surjective f ↔ surj_on f univ univ :=
by simp [surjective, surj_on, subset_def]

lemma surj_on_iff_surjective : surj_on f s univ ↔ surjective (restrict f s) :=
⟨λ H b, let ⟨a, as, e⟩ := @H b trivial in ⟨⟨a, as⟩, e⟩,
 λ H b _, let ⟨⟨a, as⟩, e⟩ := H b in ⟨a, as, e⟩⟩

lemma surj_on.image_eq_of_maps_to (h₁ : surj_on f s t) (h₂ : maps_to f s t) :
  f '' s = t :=
eq_of_subset_of_subset h₂.image_subset h₁

lemma surj_on.maps_to_compl (h : surj_on f s t) (h' : injective f) : maps_to f sᶜ tᶜ :=
λ x hs ht, let ⟨x', hx', heq⟩ := h ht in hs $ h' heq ▸ hx'

lemma maps_to.surj_on_compl (h : maps_to f s t) (h' : surjective f) : surj_on f sᶜ tᶜ :=
h'.forall.2 $ λ x ht, mem_image_of_mem _ $ λ hs, ht (h hs)

/-! ### Bijectivity -/

/-- `f` is bijective from `s` to `t` if `f` is injective on `s` and `f '' s = t`. -/
@[reducible] def bij_on (f : α → β) (s : set α) (t : set β) : Prop :=
maps_to f s t ∧ inj_on f s ∧ surj_on f s t

lemma bij_on.maps_to (h : bij_on f s t) : maps_to f s t := h.left

lemma bij_on.inj_on (h : bij_on f s t) : inj_on f s := h.right.left

lemma bij_on.surj_on (h : bij_on f s t) : surj_on f s t := h.right.right

lemma bij_on.mk (h₁ : maps_to f s t) (h₂ : inj_on f s) (h₃ : surj_on f s t) :
      bij_on f s t :=
⟨h₁, h₂, h₃⟩

lemma bij_on_empty (f : α → β) : bij_on f ∅ ∅ :=
⟨maps_to_empty f ∅, inj_on_empty f, surj_on_empty f ∅⟩

lemma bij_on.inter (h₁ : bij_on f s₁ t₁) (h₂ : bij_on f s₂ t₂) (h : inj_on f (s₁ ∪ s₂)) :
  bij_on f (s₁ ∩ s₂) (t₁ ∩ t₂) :=
⟨h₁.maps_to.inter_inter h₂.maps_to, h₁.inj_on.mono $ inter_subset_left _ _,
  h₁.surj_on.inter_inter h₂.surj_on h⟩

lemma bij_on.union (h₁ : bij_on f s₁ t₁) (h₂ : bij_on f s₂ t₂) (h : inj_on f (s₁ ∪ s₂)) :
  bij_on f (s₁ ∪ s₂) (t₁ ∪ t₂) :=
⟨h₁.maps_to.union_union h₂.maps_to, h, h₁.surj_on.union_union h₂.surj_on⟩

theorem bij_on.subset_range (h : bij_on f s t) : t ⊆ range f :=
h.surj_on.subset_range

lemma inj_on.bij_on_image (h : inj_on f s) : bij_on f s (f '' s) :=
bij_on.mk (maps_to_image f s) h (subset.refl _)

theorem bij_on.congr (h₁ : bij_on f₁ s t) (h : eq_on f₁ f₂ s) :
  bij_on f₂ s t :=
bij_on.mk (h₁.maps_to.congr h) (h₁.inj_on.congr h) (h₁.surj_on.congr h)

theorem eq_on.bij_on_iff (H : eq_on f₁ f₂ s) : bij_on f₁ s t ↔ bij_on f₂ s t :=
⟨λ h, h.congr H, λ h, h.congr H.symm⟩

lemma bij_on.image_eq (h : bij_on f s t) :
  f '' s = t :=
h.surj_on.image_eq_of_maps_to h.maps_to

theorem bij_on.comp (hg : bij_on g t p) (hf : bij_on f s t) : bij_on (g ∘ f) s p :=
bij_on.mk (hg.maps_to.comp hf.maps_to) (hg.inj_on.comp hf.inj_on hf.maps_to)
  (hg.surj_on.comp hf.surj_on)

lemma bijective_iff_bij_on_univ : bijective f ↔ bij_on f univ univ :=
iff.intro
(λ h, let ⟨inj, surj⟩ := h in
⟨maps_to_univ f _, inj.inj_on _, iff.mp surjective_iff_surj_on_univ surj⟩)
(λ h, let ⟨map, inj, surj⟩ := h in
⟨iff.mpr injective_iff_inj_on_univ inj, iff.mpr surjective_iff_surj_on_univ surj⟩)

lemma bij_on.compl (hst : bij_on f s t) (hf : bijective f) : bij_on f sᶜ tᶜ :=
⟨hst.surj_on.maps_to_compl hf.1, hf.1.inj_on _, hst.maps_to.surj_on_compl hf.2⟩

/-! ### left inverse -/

/-- `g` is a left inverse to `f` on `a` means that `g (f x) = x` for all `x ∈ a`. -/
@[reducible] def left_inv_on (f' : β → α) (f : α → β) (s : set α) : Prop :=
∀ ⦃x⦄, x ∈ s → f' (f x) = x

lemma left_inv_on.eq_on (h : left_inv_on f' f s) : eq_on (f' ∘ f) id s := h

lemma left_inv_on.eq (h : left_inv_on f' f s) {x} (hx : x ∈ s) : f' (f x) = x := h hx

lemma left_inv_on.congr_left (h₁ : left_inv_on f₁' f s)
  {t : set β} (h₁' : maps_to f s t) (heq : eq_on f₁' f₂' t) : left_inv_on f₂' f s :=
λ x hx, heq (h₁' hx) ▸ h₁ hx

theorem left_inv_on.congr_right (h₁ : left_inv_on f₁' f₁ s) (heq : eq_on f₁ f₂ s) :
  left_inv_on f₁' f₂ s :=
λ x hx, heq hx ▸ h₁ hx

theorem left_inv_on.inj_on (h : left_inv_on f₁' f s) : inj_on f s :=
λ x₁ h₁ x₂ h₂ heq,
calc
  x₁    = f₁' (f x₁) : eq.symm $ h h₁
  ...   = f₁' (f x₂) : congr_arg f₁' heq
  ...   = x₂       : h h₂

theorem left_inv_on.surj_on (h : left_inv_on f' f s) (hf : maps_to f s t) : surj_on f' t s :=
λ x hx, ⟨f x, hf hx, h hx⟩

theorem left_inv_on.maps_to (h : left_inv_on f' f s) (hf : surj_on f s t) : maps_to f' t s :=
λ y hy, let ⟨x, hs, hx⟩ := hf hy in by rwa [← hx, h hs]

theorem left_inv_on.comp (hf' : left_inv_on f' f s) (hg' : left_inv_on g' g t) (hf : maps_to f s t) :
  left_inv_on (f' ∘ g') (g ∘ f) s :=
λ x h,
calc
  (f' ∘ g') ((g ∘ f) x) = f' (f x) : congr_arg f' (hg' (hf h))
  ...                   = x        : hf' h

theorem left_inv_on.mono (hf : left_inv_on f' f s) (ht : s₁ ⊆ s) : left_inv_on f' f s₁ :=
λ x hx, hf (ht hx)

/-! ### Right inverse -/

/-- `g` is a right inverse to `f` on `b` if `f (g x) = x` for all `x ∈ b`. -/
@[reducible] def right_inv_on (f' : β → α) (f : α → β) (t : set β) : Prop :=
left_inv_on f f' t

lemma right_inv_on.eq_on (h : right_inv_on f' f t) : eq_on (f ∘ f') id t := h

lemma right_inv_on.eq (h : right_inv_on f' f t) {y} (hy : y ∈ t) : f (f' y) = y := h hy

theorem right_inv_on.congr_left (h₁ : right_inv_on f₁' f t) (heq : eq_on f₁' f₂' t) :
  right_inv_on f₂' f t :=
h₁.congr_right heq

theorem right_inv_on.congr_right (h₁ : right_inv_on f' f₁ t) (hg : maps_to f' t s)
  (heq : eq_on f₁ f₂ s) : right_inv_on f' f₂ t :=
left_inv_on.congr_left h₁ hg heq

theorem right_inv_on.surj_on (hf : right_inv_on f' f t) (hf' : maps_to f' t s) :
  surj_on f s t :=
hf.surj_on hf'

theorem right_inv_on.maps_to (h : right_inv_on f' f t) (hf : surj_on f' t s) : maps_to f s t :=
h.maps_to hf

theorem right_inv_on.comp (hf : right_inv_on f' f t) (hg : right_inv_on g' g p)
  (g'pt : maps_to g' p t) : right_inv_on (f' ∘ g') (g ∘ f) p :=
hg.comp hf g'pt

theorem right_inv_on.mono (hf : right_inv_on f' f t) (ht : t₁ ⊆ t) : right_inv_on f' f t₁ :=
hf.mono ht

theorem inj_on.right_inv_on_of_left_inv_on (hf : inj_on f s) (hf' : left_inv_on f f' t)
    (h₁ : maps_to f s t) (h₂ : maps_to f' t s) :
  right_inv_on f f' s :=
λ x h, hf (h₂ $ h₁ h) h (hf' (h₁ h))

theorem eq_on_of_left_inv_on_of_right_inv_on (h₁ : left_inv_on f₁' f s) (h₂ : right_inv_on f₂' f t)
  (h : maps_to f₂' t s) : eq_on f₁' f₂' t :=
λ y hy,
calc f₁' y = (f₁' ∘ f ∘ f₂') y : congr_arg f₁' (h₂ hy).symm
      ...  = f₂' y              : h₁ (h hy)

theorem surj_on.left_inv_on_of_right_inv_on (hf : surj_on f s t) (hf' : right_inv_on f f' s) :
  left_inv_on f f' t :=
λ y hy, let ⟨x, hx, heq⟩ := hf hy in by rw [← heq, hf' hx]

/-! ### Two-side inverses -/

/-- `g` is an inverse to `f` viewed as a map from `a` to `b` -/
@[reducible] def inv_on (g : β → α) (f : α → β) (s : set α) (t : set β) : Prop :=
left_inv_on g f s ∧ right_inv_on g f t

lemma inv_on.symm (h : inv_on f' f s t) : inv_on f f' t s := ⟨h.right, h.left⟩

lemma inv_on.mono (h : inv_on f' f s t) (hs : s₁ ⊆ s) (ht : t₁ ⊆ t) : inv_on f' f s₁ t₁ :=
⟨h.1.mono hs, h.2.mono ht⟩

/-- If functions `f'` and `f` are inverse on `s` and `t`, `f` maps `s` into `t`, and `f'` maps `t`
into `s`, then `f` is a bijection between `s` and `t`. The `maps_to` arguments can be deduced from
`surj_on` statements using `left_inv_on.maps_to` and `right_inv_on.maps_to`. -/
theorem inv_on.bij_on (h : inv_on f' f s t) (hf : maps_to f s t) (hf' : maps_to f' t s) :
  bij_on f s t :=
⟨hf, h.left.inj_on, h.right.surj_on hf'⟩

/-! ### `inv_fun_on` is a left/right inverse -/

theorem inj_on.left_inv_on_inv_fun_on [nonempty α] (h : inj_on f s) :
  left_inv_on (inv_fun_on f s) f s :=
λ x hx, inv_fun_on_eq' h hx

theorem surj_on.right_inv_on_inv_fun_on [nonempty α] (h : surj_on f s t) :
  right_inv_on (inv_fun_on f s) f t :=
λ y hy, inv_fun_on_eq $ mem_image_iff_bex.1 $ h hy

theorem bij_on.inv_on_inv_fun_on [nonempty α] (h : bij_on f s t) :
  inv_on (inv_fun_on f s) f s t :=
⟨h.inj_on.left_inv_on_inv_fun_on, h.surj_on.right_inv_on_inv_fun_on⟩

theorem surj_on.inv_on_inv_fun_on [nonempty α] (h : surj_on f s t) :
  inv_on (inv_fun_on f s) f (inv_fun_on f s '' t) t :=
begin
  refine ⟨_, h.right_inv_on_inv_fun_on⟩,
  rintros _ ⟨y, hy, rfl⟩,
  rw [h.right_inv_on_inv_fun_on hy]
end

theorem surj_on.maps_to_inv_fun_on [nonempty α] (h : surj_on f s t) :
  maps_to (inv_fun_on f s) t s :=
λ y hy, mem_preimage.2 $ inv_fun_on_mem $ mem_image_iff_bex.1 $ h hy

theorem surj_on.bij_on_subset [nonempty α] (h : surj_on f s t) :
  bij_on f (inv_fun_on f s '' t) t :=
begin
  refine h.inv_on_inv_fun_on.bij_on _ (maps_to_image _ _),
  rintros _ ⟨y, hy, rfl⟩,
  rwa [h.right_inv_on_inv_fun_on hy]
end

theorem surj_on_iff_exists_bij_on_subset :
  surj_on f s t ↔ ∃ s' ⊆ s, bij_on f s' t :=
begin
  split,
  { rcases eq_empty_or_nonempty t with rfl|ht,
    { exact λ _, ⟨∅, empty_subset _, bij_on_empty f⟩ },
    { assume h,
      haveI : nonempty α := ⟨classical.some (h.comap_nonempty ht)⟩,
      exact ⟨_, h.maps_to_inv_fun_on.image_subset, h.bij_on_subset⟩ }},
  { rintros ⟨s', hs', hfs'⟩,
    exact hfs'.surj_on.mono hs' (subset.refl _) }
end

end set

/-! ### Piecewise defined function -/

namespace set

variables {δ : α → Sort y} (s : set α) (f g : Πi, δ i)

@[simp] lemma piecewise_empty [∀i : α, decidable (i ∈ (∅ : set α))] : piecewise ∅ f g = g :=
by { ext i, simp [piecewise] }

@[simp] lemma piecewise_univ [∀i : α, decidable (i ∈ (set.univ : set α))] :
  piecewise set.univ f g = f :=
by { ext i, simp [piecewise] }

@[simp] lemma piecewise_insert_self {j : α} [∀i, decidable (i ∈ insert j s)] :
  (insert j s).piecewise f g j = f j :=
by simp [piecewise]

variable [∀j, decidable (j ∈ s)]

instance compl.decidable_mem (j : α) : decidable (j ∈ sᶜ) := not.decidable

lemma piecewise_insert [decidable_eq α] (j : α) [∀i, decidable (i ∈ insert j s)] :
  (insert j s).piecewise f g = function.update (s.piecewise f g) j (f j) :=
begin
  simp [piecewise],
  ext i,
  by_cases h : i = j,
  { rw h, simp },
  { by_cases h' : i ∈ s; simp [h, h'] }
end

@[simp, priority 990]
lemma piecewise_eq_of_mem {i : α} (hi : i ∈ s) : s.piecewise f g i = f i :=
by simp [piecewise, hi]

@[simp, priority 990]
lemma piecewise_eq_of_not_mem {i : α} (hi : i ∉ s) : s.piecewise f g i = g i :=
by simp [piecewise, hi]

lemma piecewise_eq_on (f g : α → β) : eq_on (s.piecewise f g) f s :=
λ _, piecewise_eq_of_mem _ _ _

lemma piecewise_eq_on_compl (f g : α → β) : eq_on (s.piecewise f g) g sᶜ :=
λ _, piecewise_eq_of_not_mem _ _ _

@[simp, priority 990]
lemma piecewise_insert_of_ne {i j : α} (h : i ≠ j) [∀i, decidable (i ∈ insert j s)] :
  (insert j s).piecewise f g i = s.piecewise f g i :=
by simp [piecewise, h]

@[simp] lemma piecewise_compl [∀ i, decidable (i ∈ sᶜ)] : sᶜ.piecewise f g = s.piecewise g f :=
funext $ λ x, if hx : x ∈ s then by simp [hx] else by simp [hx]

@[simp] lemma piecewise_range_comp {ι : Sort*} (f : ι → α) [Π j, decidable (j ∈ range f)]
  (g₁ g₂ : α → β) :
  (range f).piecewise g₁ g₂ ∘ f = g₁ ∘ f :=
comp_eq_of_eq_on_range $ piecewise_eq_on _ _ _

lemma piecewise_preimage (f g : α → β) (t) :
  s.piecewise f g ⁻¹' t = s ∩ f ⁻¹' t ∪ sᶜ ∩ g ⁻¹' t :=
ext $ λ x, by by_cases x ∈ s; simp *

lemma comp_piecewise (h : β → γ) {f g : α → β} {x : α} :
  h (s.piecewise f g x) = s.piecewise (h ∘ f) (h ∘ g) x :=
by by_cases hx : x ∈ s; simp [hx]

@[simp] lemma piecewise_same : s.piecewise f f = f :=
by { ext x, by_cases hx : x ∈ s; simp [hx] }

lemma range_piecewise (f g : α → β) : range (s.piecewise f g) = f '' s ∪ g '' sᶜ :=
begin
  ext y, split,
  { rintro ⟨x, rfl⟩, by_cases h : x ∈ s;[left, right]; use x; simp [h] },
  { rintro (⟨x, hx, rfl⟩|⟨x, hx, rfl⟩); use x; simp * at * }
end

end set

lemma strict_mono_incr_on.inj_on [linear_order α] [preorder β] {f : α → β} {s : set α}
  (H : strict_mono_incr_on f s) :
  s.inj_on f :=
λ x hx y hy hxy, show ordering.eq.compares x y, from (H.compares hx hy).1 hxy

lemma strict_mono_decr_on.inj_on [linear_order α] [preorder β] {f : α → β} {s : set α}
  (H : strict_mono_decr_on f s) :
  s.inj_on f :=
@strict_mono_incr_on.inj_on α (order_dual β) _ _ f s H

namespace function

open set

variables {fa : α → α} {fb : β → β} {f : α → β} {g : β → γ} {s t : set α}

lemma injective.comp_inj_on (hg : injective g) (hf : s.inj_on f) : s.inj_on (g ∘ f) :=
(hg.inj_on univ).comp hf (maps_to_univ _ _)

lemma surjective.surj_on (hf : surjective f) (s : set β) :
  surj_on f univ s :=
(surjective_iff_surj_on_univ.1 hf).mono (subset.refl _) (subset_univ _)

namespace semiconj

lemma maps_to_image (h : semiconj f fa fb) (ha : maps_to fa s t) :
  maps_to fb (f '' s) (f '' t) :=
λ y ⟨x, hx, hy⟩, hy ▸ ⟨fa x, ha hx, h x⟩

lemma maps_to_range (h : semiconj f fa fb) : maps_to fb (range f) (range f) :=
λ y ⟨x, hy⟩, hy ▸ ⟨fa x, h x⟩

lemma surj_on_image (h : semiconj f fa fb) (ha : surj_on fa s t) :
  surj_on fb (f '' s) (f '' t) :=
begin
  rintros y ⟨x, hxt, rfl⟩,
  rcases ha hxt with ⟨x, hxs, rfl⟩,
  rw [h x],
  exact mem_image_of_mem _ (mem_image_of_mem _ hxs)
end

lemma surj_on_range (h : semiconj f fa fb) (ha : surjective fa) :
  surj_on fb (range f) (range f) :=
by { rw ← image_univ, exact h.surj_on_image (ha.surj_on univ) }

lemma inj_on_image (h : semiconj f fa fb) (ha : inj_on fa s) (hf : inj_on f (fa '' s)) :
  inj_on fb (f '' s) :=
begin
  rintros _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ H,
  simp only [← h.eq] at H,
  exact congr_arg f (ha hx hy $ hf (mem_image_of_mem fa hx) (mem_image_of_mem fa hy) H)
end

lemma inj_on_range (h : semiconj f fa fb) (ha : injective fa) (hf : inj_on f (range fa)) :
  inj_on fb (range f) :=
by { rw ← image_univ at *, exact h.inj_on_image (ha.inj_on univ) hf }

lemma bij_on_image (h : semiconj f fa fb) (ha : bij_on fa s t) (hf : inj_on f t) :
  bij_on fb (f '' s) (f '' t) :=
⟨h.maps_to_image ha.maps_to, h.inj_on_image ha.inj_on (ha.image_eq.symm ▸ hf),
  h.surj_on_image ha.surj_on⟩

lemma bij_on_range (h : semiconj f fa fb) (ha : bijective fa) (hf : injective f) :
  bij_on fb (range f) (range f) :=
begin
  rw [← image_univ],
  exact h.bij_on_image (bijective_iff_bij_on_univ.1 ha) (hf.inj_on univ)
end

lemma maps_to_preimage (h : semiconj f fa fb) {s t : set β} (hb : maps_to fb s t) :
  maps_to fa (f ⁻¹' s) (f ⁻¹' t) :=
λ x hx, by simp only [mem_preimage, h x, hb hx]

lemma inj_on_preimage (h : semiconj f fa fb) {s : set β} (hb : inj_on fb s)
  (hf : inj_on f (f ⁻¹' s)) :
  inj_on fa (f ⁻¹' s) :=
begin
  intros x hx y hy H,
  have := congr_arg f H,
  rw [h.eq, h.eq] at this,
  exact hf hx hy (hb hx hy this)
end

end semiconj

lemma update_comp_eq_of_not_mem_range [decidable_eq β]
  (g : β → γ) {f : α → β} {i : β} (a : γ) (h : i ∉ set.range f) :
  (function.update g i a) ∘ f = g ∘ f :=
begin
  ext p,
  have : f p ≠ i,
  { by_contradiction H,
    push_neg at H,
    rw ← H at h,
    exact h (set.mem_range_self _) },
  simp [this],
end

lemma update_comp_eq_of_injective [decidable_eq α] [decidable_eq β]
  (g : β → γ) {f : α → β} (hf : function.injective f) (i : α) (a : γ) :
  (function.update g (f i) a) ∘ f = function.update (g ∘ f) i a :=
begin
  ext j,
  by_cases h : j = i,
  { rw h, simp },
  { have : f j ≠ f i := hf.ne h,
    simp [h, this] }
end

end function
