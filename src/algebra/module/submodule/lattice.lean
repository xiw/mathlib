import algebra.module.submodule.linear_map
import algebra.pointwise

universes w

variables {R M M₂ M₃ ι : Type*}

namespace submodule

section add_comm_monoid

variables [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃]
variables [semimodule R M] [semimodule R M₂] [semimodule R M₃]
variables (p p' : submodule R M) (q q' : submodule R M₂)
variables {r : R} {x y : M}
open set

instance : partial_order (submodule R M) :=
{ le := λ p p', ∀ ⦃x⦄, x ∈ p → x ∈ p',
  ..partial_order.lift (coe : submodule R M → set M) coe_injective }

variables {p p'}

lemma le_def : p ≤ p' ↔ (p : set M) ⊆ p' := iff.rfl

lemma le_def' : p ≤ p' ↔ ∀ x ∈ p, x ∈ p' := iff.rfl

lemma lt_def : p < p' ↔ (p : set M) ⊂ p' := iff.rfl

lemma not_le_iff_exists : ¬ (p ≤ p') ↔ ∃ x ∈ p, x ∉ p' := not_subset

lemma exists_of_lt {p p' : submodule R M} : p < p' → ∃ x ∈ p', x ∉ p := exists_of_ssubset

lemma lt_iff_le_and_exists : p < p' ↔ p ≤ p' ∧ ∃ x ∈ p', x ∉ p :=
by rw [lt_iff_le_not_le, not_le_iff_exists]

/-- If two submodules `p` and `p'` satisfy `p ⊆ p'`, then `of_le p p'` is the linear map version of
this inclusion. -/
def of_le (h : p ≤ p') : p →ₗ[R] p' :=
p.subtype.cod_restrict p' $ λ ⟨x, hx⟩, h hx

@[simp] theorem coe_of_le (h : p ≤ p') (x : p) :
  (of_le h x : M) = x := rfl

theorem of_le_apply (h : p ≤ p') (x : p) : of_le h x = ⟨x, h x.2⟩ := rfl

variables (p p')

lemma subtype_comp_of_le (p q : submodule R M) (h : p ≤ q) :
  q.subtype.comp (of_le h) = p.subtype :=
by { ext ⟨b, hb⟩, refl }

/-- The set `{0}` is the bottom element of the lattice of submodules. -/
instance : has_bot (submodule R M) :=
⟨{ carrier := {0}, smul_mem' := by simp { contextual := tt }, .. (⊥ : add_submonoid M)}⟩

instance inhabited' : inhabited (submodule R M) := ⟨⊥⟩

@[simp] lemma bot_coe : ((⊥ : submodule R M) : set M) = {0} := rfl

section
variables (R)
@[simp] lemma mem_bot : x ∈ (⊥ : submodule R M) ↔ x = 0 := mem_singleton_iff
end

lemma nonzero_mem_of_bot_lt {I : submodule R M} (bot_lt : ⊥ < I) : ∃ a : I, a ≠ 0 :=
begin
  have h := (submodule.lt_iff_le_and_exists.1 bot_lt).2,
  tidy,
end

instance : order_bot (submodule R M) :=
{ bot := ⊥,
  bot_le := λ p x, by simp {contextual := tt},
  ..submodule.partial_order }

protected lemma eq_bot_iff (p : submodule R M) : p = ⊥ ↔ ∀ x ∈ p, x = (0 : M) :=
⟨ λ h, h.symm ▸ λ x hx, (mem_bot R).mp hx,
  λ h, eq_bot_iff.mpr (λ x hx, (mem_bot R).mpr (h x hx)) ⟩

protected lemma ne_bot_iff (p : submodule R M) : p ≠ ⊥ ↔ ∃ x ∈ p, x ≠ (0 : M) :=
by { haveI := classical.prop_decidable, simp_rw [ne.def, p.eq_bot_iff, not_forall] }

/-- The universal set is the top element of the lattice of submodules. -/
instance : has_top (submodule R M) :=
⟨{ carrier := univ, smul_mem' := λ _ _ _, trivial, .. (⊤ : add_submonoid M)}⟩

@[simp] lemma top_coe : ((⊤ : submodule R M) : set M) = univ := rfl

@[simp] lemma mem_top : x ∈ (⊤ : submodule R M) := trivial

lemma eq_bot_of_zero_eq_one (zero_eq_one : (0 : R) = 1) : p = ⊥ :=
by ext x; simp [semimodule.eq_zero_of_zero_eq_one x zero_eq_one]

instance : order_top (submodule R M) :=
{ top := ⊤,
  le_top := λ p x _, trivial,
  ..submodule.partial_order }

instance : has_Inf (submodule R M) :=
⟨λ S, {
  carrier   := ⋂ s ∈ S, (s : set M),
  zero_mem' := by simp,
  add_mem'  := by simp [add_mem] {contextual := tt},
  smul_mem' := by simp [smul_mem] {contextual := tt} }⟩

private lemma Inf_le' {S : set (submodule R M)} {p} : p ∈ S → Inf S ≤ p :=
bInter_subset_of_mem

private lemma le_Inf' {S : set (submodule R M)} {p} : (∀p' ∈ S, p ≤ p') → p ≤ Inf S :=
subset_bInter

instance : has_inf (submodule R M) :=
⟨λ p p', {
  carrier   := p ∩ p',
  zero_mem' := by simp,
  add_mem'  := by simp [add_mem] {contextual := tt},
  smul_mem' := by simp [smul_mem] {contextual := tt} }⟩

instance : complete_lattice (submodule R M) :=
{ sup          := λ a b, Inf {x | a ≤ x ∧ b ≤ x},
  le_sup_left  := λ a b, le_Inf' $ λ x ⟨ha, hb⟩, ha,
  le_sup_right := λ a b, le_Inf' $ λ x ⟨ha, hb⟩, hb,
  sup_le       := λ a b c h₁ h₂, Inf_le' ⟨h₁, h₂⟩,
  inf          := (⊓),
  le_inf       := λ a b c, subset_inter,
  inf_le_left  := λ a b, inter_subset_left _ _,
  inf_le_right := λ a b, inter_subset_right _ _,
  Sup          := λtt, Inf {t | ∀t'∈tt, t' ≤ t},
  le_Sup       := λ s p hs, le_Inf' $ λ p' hp', hp' _ hs,
  Sup_le       := λ s p hs, Inf_le' hs,
  Inf          := Inf,
  le_Inf       := λ s a, le_Inf',
  Inf_le       := λ s a, Inf_le',
  ..submodule.order_top,
  ..submodule.order_bot }

instance add_comm_monoid_submodule : add_comm_monoid (submodule R M) :=
{ add := (⊔),
  add_assoc := λ _ _ _, sup_assoc,
  zero := ⊥,
  zero_add := λ _, bot_sup_eq,
  add_zero := λ _, sup_bot_eq,
  add_comm := λ _ _, sup_comm }

@[simp] lemma add_eq_sup (p q : submodule R M) : p + q = p ⊔ q := rfl
@[simp] lemma zero_eq_bot : (0 : submodule R M) = ⊥ := rfl

lemma eq_top_iff' {p : submodule R M} : p = ⊤ ↔ ∀ x, x ∈ p :=
eq_top_iff.trans ⟨λ h x, @h x trivial, λ h x _, h x⟩

lemma bot_ne_top [nontrivial M] : (⊥ : submodule R M) ≠ ⊤ :=
λ h, let ⟨a, ha⟩ := exists_ne (0 : M) in ha $ (mem_bot R).1 $ (eq_top_iff.1 h) trivial

@[simp] theorem inf_coe : (p ⊓ p' : set M) = p ∩ p' := rfl

@[simp] theorem mem_inf {p p' : submodule R M} :
  x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' := iff.rfl

@[simp] theorem Inf_coe (P : set (submodule R M)) : (↑(Inf P) : set M) = ⋂ p ∈ P, ↑p := rfl

@[simp] theorem infi_coe {ι} (p : ι → submodule R M) :
  (↑⨅ i, p i : set M) = ⋂ i, ↑(p i) :=
by rw [infi, Inf_coe]; ext a; simp; exact
⟨λ h i, h _ i rfl, λ h i x e, e ▸ h _⟩

@[simp] lemma mem_Inf {S : set (submodule R M)} {x : M} : x ∈ Inf S ↔ ∀ p ∈ S, x ∈ p :=
set.mem_bInter_iff

@[simp] theorem mem_infi {ι} (p : ι → submodule R M) :
  x ∈ (⨅ i, p i) ↔ ∀ i, x ∈ p i :=
by rw [← mem_coe, infi_coe, mem_Inter]; refl

theorem disjoint_def {p p' : submodule R M} :
  disjoint p p' ↔ ∀ x ∈ p, x ∈ p' → x = (0:M) :=
show (∀ x, x ∈ p ∧ x ∈ p' → x ∈ ({0} : set M)) ↔ _, by simp

theorem mem_right_iff_eq_zero_of_disjoint {p p' : submodule R M} (h : disjoint p p') {x : p} :
  (x:M) ∈ p' ↔ x = 0 :=
⟨λ hx, coe_eq_zero.1 $ disjoint_def.1 h x x.2 hx, λ h, h.symm ▸ p'.zero_mem⟩

theorem mem_left_iff_eq_zero_of_disjoint {p p' : submodule R M} (h : disjoint p p') {x : p'} :
  (x:M) ∈ p ↔ x = 0 :=
⟨λ hx, coe_eq_zero.1 $ disjoint_def.1 h x hx x.2, λ h, h.symm ▸ p.zero_mem⟩

lemma map_mono {f : M →ₗ[R] M₂} {p p' : submodule R M} : p ≤ p' → map f p ≤ map f p' :=
image_subset _

@[simp] lemma map_zero : map (0 : M →ₗ[R] M₂) p = ⊥ :=
have ∃ (x : M), x ∈ p := ⟨0, p.zero_mem⟩,
ext $ by simp [this, eq_comm]

lemma comap_mono {f : M →ₗ[R] M₂} {q q' : submodule R M₂} : q ≤ q' → comap f q ≤ comap f q' :=
preimage_mono

lemma map_le_iff_le_comap {f : M →ₗ[R] M₂} {p : submodule R M} {q : submodule R M₂} :
  map f p ≤ q ↔ p ≤ comap f q := image_subset_iff

lemma gc_map_comap (f : M →ₗ[R] M₂) : galois_connection (map f) (comap f)
| p q := map_le_iff_le_comap

@[simp] lemma map_bot (f : M →ₗ[R] M₂) : map f ⊥ = ⊥ :=
(gc_map_comap f).l_bot

@[simp] lemma map_sup (f : M →ₗ[R] M₂) : map f (p ⊔ p') = map f p ⊔ map f p' :=
(gc_map_comap f).l_sup

@[simp] lemma map_supr {ι : Sort*} (f : M →ₗ[R] M₂) (p : ι → submodule R M) :
  map f (⨆i, p i) = (⨆i, map f (p i)) :=
(gc_map_comap f).l_supr

@[simp] lemma comap_top (f : M →ₗ[R] M₂) : comap f ⊤ = ⊤ := rfl

@[simp] lemma comap_inf (f : M →ₗ[R] M₂) : comap f (q ⊓ q') = comap f q ⊓ comap f q' := rfl

@[simp] lemma comap_infi {ι : Sort*} (f : M →ₗ[R] M₂) (p : ι → submodule R M₂) :
  comap f (⨅i, p i) = (⨅i, comap f (p i)) :=
(gc_map_comap f).u_infi

@[simp] lemma comap_zero : comap (0 : M →ₗ[R] M₂) q = ⊤ :=
ext $ by simp

lemma map_comap_le (f : M →ₗ[R] M₂) (q : submodule R M₂) : map f (comap f q) ≤ q :=
(gc_map_comap f).l_u_le _

lemma le_comap_map (f : M →ₗ[R] M₂) (p : submodule R M) : p ≤ comap f (map f p) :=
(gc_map_comap f).le_u_l _

--TODO(Mario): is there a way to prove this from order properties?
lemma map_inf_eq_map_inf_comap {f : M →ₗ[R] M₂}
  {p : submodule R M} {p' : submodule R M₂} :
  map f p ⊓ p' = map f (p ⊓ comap f p') :=
le_antisymm
  (by rintro _ ⟨⟨x, h₁, rfl⟩, h₂⟩; exact ⟨_, ⟨h₁, h₂⟩, rfl⟩)
  (le_inf (map_mono inf_le_left) (map_le_iff_le_comap.2 inf_le_right))

lemma map_comap_subtype : map p.subtype (comap p.subtype p') = p ⊓ p' :=
ext $ λ x, ⟨by rintro ⟨⟨_, h₁⟩, h₂, rfl⟩; exact ⟨h₁, h₂⟩, λ ⟨h₁, h₂⟩, ⟨⟨_, h₁⟩, h₂, rfl⟩⟩

lemma eq_zero_of_bot_submodule : ∀(b : (⊥ : submodule R M)), b = 0
| ⟨b', hb⟩ := subtype.eq $ show b' = 0, from (mem_bot R).1 hb

section
variables (R)

/-- The span of a set `s ⊆ M` is the smallest submodule of M that contains `s`. -/
def span (s : set M) : submodule R M := Inf {p | s ⊆ p}
end

variables {s t : set M}
lemma mem_span : x ∈ span R s ↔ ∀ p : submodule R M, s ⊆ p → x ∈ p :=
mem_bInter_iff

lemma subset_span : s ⊆ span R s :=
λ x h, mem_span.2 $ λ p hp, hp h

lemma span_le {p} : span R s ≤ p ↔ s ⊆ p :=
⟨subset.trans subset_span, λ ss x h, mem_span.1 h _ ss⟩

lemma span_mono (h : s ⊆ t) : span R s ≤ span R t :=
span_le.2 $ subset.trans h subset_span

lemma span_eq_of_le (h₁ : s ⊆ p) (h₂ : p ≤ span R s) : span R s = p :=
le_antisymm (span_le.2 h₁) h₂

@[simp] lemma span_eq : span R (p : set M) = p :=
span_eq_of_le _ (subset.refl _) subset_span

lemma map_span (f : M →ₗ[R] M₂) (s : set M) :
  (span R s).map f = span R (f '' s) :=
eq.symm $ span_eq_of_le _ (set.image_subset f subset_span) $
map_le_iff_le_comap.2 $ span_le.2 $ λ x hx, subset_span ⟨x, hx, rfl⟩

/-- An induction principle for span membership. If `p` holds for 0 and all elements of `s`, and is
preserved under addition and scalar multiplication, then `p` holds for all elements of the span of
`s`. -/
@[elab_as_eliminator] lemma span_induction {p : M → Prop} (h : x ∈ span R s)
  (Hs : ∀ x ∈ s, p x) (H0 : p 0)
  (H1 : ∀ x y, p x → p y → p (x + y))
  (H2 : ∀ (a:R) x, p x → p (a • x)) : p x :=
(@span_le _ _ _ _ _ _ ⟨p, H0, H1, H2⟩).2 Hs h

section
variables (R M)

/-- `span` forms a Galois insertion with the coercion from submodule to set. -/
protected def gi : galois_insertion (@span R M _ _ _) coe :=
{ choice := λ s _, span R s,
  gc := λ s t, span_le,
  le_l_u := λ s, subset_span,
  choice_eq := λ s h, rfl }

end

@[simp] lemma span_empty : span R (∅ : set M) = ⊥ :=
(submodule.gi R M).gc.l_bot

@[simp] lemma span_univ : span R (univ : set M) = ⊤ :=
eq_top_iff.2 $ le_def.2 $ subset_span

lemma span_union (s t : set M) : span R (s ∪ t) = span R s ⊔ span R t :=
(submodule.gi R M).gc.l_sup

lemma span_Union {ι} (s : ι → set M) : span R (⋃ i, s i) = ⨆ i, span R (s i) :=
(submodule.gi R M).gc.l_supr

@[simp] theorem coe_supr_of_directed {ι} [hι : nonempty ι]
  (S : ι → submodule R M) (H : directed (≤) S) :
  ((supr S : submodule R M) : set M) = ⋃ i, S i :=
begin
  refine subset.antisymm _ (Union_subset $ le_supr S),
  suffices : (span R (⋃ i, (S i : set M)) : set M) ⊆ ⋃ (i : ι), ↑(S i),
    by simpa only [span_Union, span_eq] using this,
  refine (λ x hx, span_induction hx (λ _, id) _ _ _);
    simp only [mem_Union, exists_imp_distrib],
  { exact hι.elim (λ i, ⟨i, (S i).zero_mem⟩) },
  { intros x y i hi j hj,
    rcases H i j with ⟨k, ik, jk⟩,
    exact ⟨k, add_mem _ (ik hi) (jk hj)⟩ },
  { exact λ a x i hi, ⟨i, smul_mem _ a hi⟩ },
end

lemma mem_sup_left {S T : submodule R M} : ∀ {x : M}, x ∈ S → x ∈ S ⊔ T :=
show S ≤ S ⊔ T, from le_sup_left

lemma mem_sup_right {S T : submodule R M} : ∀ {x : M}, x ∈ T → x ∈ S ⊔ T :=
show T ≤ S ⊔ T, from le_sup_right

lemma mem_supr_of_mem {ι : Sort*} {b : M} {p : ι → submodule R M} (i : ι) (h : b ∈ p i) :
  b ∈ (⨆i, p i) :=
have p i ≤ (⨆i, p i) := le_supr p i,
@this b h

lemma mem_Sup_of_mem {S : set (submodule R M)} {s : submodule R M}
  (hs : s ∈ S) : ∀ {x : M}, x ∈ s → x ∈ Sup S :=
show s ≤ Sup S, from le_Sup hs

@[simp] theorem mem_supr_of_directed {ι} [nonempty ι]
  (S : ι → submodule R M) (H : directed (≤) S) {x} :
  x ∈ supr S ↔ ∃ i, x ∈ S i :=
by { rw [← mem_coe, coe_supr_of_directed S H, mem_Union], refl }

theorem mem_Sup_of_directed {s : set (submodule R M)}
  {z} (hs : s.nonempty) (hdir : directed_on (≤) s) :
  z ∈ Sup s ↔ ∃ y ∈ s, z ∈ y :=
begin
  haveI : nonempty s := hs.to_subtype,
  simp only [Sup_eq_supr', mem_supr_of_directed _ hdir.directed_coe, set_coe.exists, subtype.coe_mk]
end

section

variables {p p'}

lemma mem_sup : x ∈ p ⊔ p' ↔ ∃ (y ∈ p) (z ∈ p'), y + z = x :=
⟨λ h, begin
  rw [← span_eq p, ← span_eq p', ← span_union] at h,
  apply span_induction h,
  { rintro y (h | h),
    { exact ⟨y, h, 0, by simp, by simp⟩ },
    { exact ⟨0, by simp, y, h, by simp⟩ } },
  { exact ⟨0, by simp, 0, by simp⟩ },
  { rintro _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩,
    exact ⟨_, add_mem _ hy₁ hy₂, _, add_mem _ hz₁ hz₂, by simp [add_assoc]; cc⟩ },
  { rintro a _ ⟨y, hy, z, hz, rfl⟩,
    exact ⟨_, smul_mem _ a hy, _, smul_mem _ a hz, by simp [smul_add]⟩ }
end,
by rintro ⟨y, hy, z, hz, rfl⟩; exact add_mem _
  ((le_sup_left : p ≤ p ⊔ p') hy)
  ((le_sup_right : p' ≤ p ⊔ p') hz)⟩

lemma mem_sup' : x ∈ p ⊔ p' ↔ ∃ (y : p) (z : p'), (y:M) + z = x :=
mem_sup.trans $ by simp only [submodule.exists, coe_mk]

end

lemma mem_span_singleton_self (x : M) : x ∈ span R ({x} : set M) := subset_span rfl

lemma nontrivial_span_singleton {x : M} (h : x ≠ 0) : nontrivial (submodule.span R ({x} : set M)) :=
⟨begin
    use [0, x, submodule.mem_span_singleton_self x],
    intros H,
    rw [eq_comm, submodule.mk_eq_zero] at H,
    exact h H
end⟩

lemma mem_span_singleton {y : M} : x ∈ span R ({y} : set M) ↔ ∃ a:R, a • y = x :=
⟨λ h, begin
  apply span_induction h,
  { rintro y (rfl|⟨⟨⟩⟩), exact ⟨1, by simp⟩ },
  { exact ⟨0, by simp⟩ },
  { rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩,
    exact ⟨a + b, by simp [add_smul]⟩ },
  { rintro a _ ⟨b, rfl⟩,
    exact ⟨a * b, by simp [smul_smul]⟩ }
end,
by rintro ⟨a, y, rfl⟩; exact
  smul_mem _ _ (subset_span $ by simp)⟩

lemma le_span_singleton_iff {s : submodule R M} {v₀ : M} :
  s ≤ span R {v₀} ↔ ∀ v ∈ s, ∃ r : R, r • v₀ = v :=
by simp_rw [le_def', mem_span_singleton]

lemma span_singleton_eq_range (y : M) : (span R ({y} : set M) : set M) = range ((• y) : R → M) :=
set.ext $ λ x, mem_span_singleton

lemma span_singleton_smul_le (r : R) (x : M) : span R ({r • x} : set M) ≤ span R {x} :=
begin
  rw [span_le, set.singleton_subset_iff, mem_coe],
  exact smul_mem _ _ (mem_span_singleton_self _)
end

lemma span_singleton_smul_eq {K E : Type*} [division_ring K] [add_comm_group E] [module K E]
  {r : K} (x : E) (hr : r ≠ 0) : span K ({r • x} : set E) = span K {x} :=
begin
  refine le_antisymm (span_singleton_smul_le r x) _,
  convert span_singleton_smul_le r⁻¹ (r • x),
  exact (inv_smul_smul' hr _).symm
end

lemma disjoint_span_singleton {K E : Type*} [division_ring K] [add_comm_group E] [module K E]
  {s : submodule K E} {x : E} :
  disjoint s (span K {x}) ↔ (x ∈ s → x = 0) :=
begin
  refine disjoint_def.trans ⟨λ H hx, H x hx $ subset_span $ mem_singleton x, _⟩,
  assume H y hy hyx,
  obtain ⟨c, hc⟩ := mem_span_singleton.1 hyx,
  subst y,
  classical, by_cases hc : c = 0, by simp only [hc, zero_smul],
  rw [s.smul_mem_iff hc] at hy,
  rw [H hy, smul_zero]
end

lemma mem_span_insert {y} : x ∈ span R (insert y s) ↔ ∃ (a:R) (z ∈ span R s), x = a • y + z :=
begin
  simp only [← union_singleton, span_union, mem_sup, mem_span_singleton, exists_prop,
    exists_exists_eq_and],
  rw [exists_comm],
  simp only [eq_comm, add_comm, exists_and_distrib_left]
end

lemma span_insert_eq_span (h : x ∈ span R s) : span R (insert x s) = span R s :=
span_eq_of_le _ (set.insert_subset.mpr ⟨h, subset_span⟩) (span_mono $ subset_insert _ _)

lemma span_span : span R (span R s : set M) = span R s := span_eq _

lemma span_eq_bot : span R (s : set M) = ⊥ ↔ ∀ x ∈ s, (x:M) = 0 :=
eq_bot_iff.trans ⟨
  λ H x h, (mem_bot R).1 $ H $ subset_span h,
  λ H, span_le.2 (λ x h, (mem_bot R).2 $ H x h)⟩

@[simp] lemma span_singleton_eq_bot : span R ({x} : set M) = ⊥ ↔ x = 0 :=
span_eq_bot.trans $ by simp

@[simp] lemma span_zero : span R (0 : set M) = ⊥ := by rw [←singleton_zero, span_singleton_eq_bot]

@[simp] lemma span_image (f : M →ₗ[R] M₂) : span R (f '' s) = map f (span R s) :=
span_eq_of_le _ (image_subset _ subset_span) $ map_le_iff_le_comap.2 $
span_le.2 $ image_subset_iff.1 subset_span

lemma linear_eq_on (s : set M) {f g : M →ₗ[R] M₂} (H : ∀x∈s, f x = g x) {x} (h : x ∈ span R s) :
  f x = g x :=
by apply span_induction h H; simp {contextual := tt}

lemma linear_map.ext_on {v : ι → M} {f g : M →ₗ[R] M₂} (hv : span R (range v) = ⊤)
  (h : ∀i, f (v i) = g (v i)) : f = g :=
begin
  apply linear_map.ext (λ x, linear_eq_on (range v) _ (eq_top_iff'.1 hv _)),
  exact (λ y hy, exists.elim (set.mem_range.1 hy) (λ i hi, by rw ←hi; exact h i))
end

lemma supr_eq_span {ι : Sort w} (p : ι → submodule R M) :
  (⨆ (i : ι), p i) = submodule.span R (⋃ (i : ι), ↑(p i)) :=
le_antisymm
  (supr_le $ assume i, subset.trans (assume m hm, set.mem_Union.mpr ⟨i, hm⟩) subset_span)
  (span_le.mpr $ Union_subset_iff.mpr $ assume i m hm, mem_supr_of_mem i hm)

lemma span_singleton_le_iff_mem (m : M) (p : submodule R M) :
  span R {m} ≤ p ↔ m ∈ p :=
by rw [span_le, singleton_subset_iff, mem_coe]

lemma lt_add_iff_not_mem {I : submodule R M} {a : M} : I < I + span R {a} ↔ a ∉ I :=
begin
  split,
  { intro h,
    by_contra akey,
    have h1 : I + span R {a} ≤ I,
    { simp only [add_eq_sup, sup_le_iff],
      split,
      { exact le_refl I, },
      { exact (span_singleton_le_iff_mem a I).mpr akey, } },
    have h2 := gt_of_ge_of_gt h1 h,
    exact lt_irrefl I h2, },
  { intro h,
    apply lt_iff_le_and_exists.mpr, split,
    simp only [add_eq_sup, le_sup_left],
    use a,
    split, swap, { assumption, },
    { have : span R {a} ≤ I + span R{a} := le_sup_right,
      exact this (mem_span_singleton_self a), } },
end

lemma mem_supr {ι : Sort w} (p : ι → submodule R M) {m : M} :
  (m ∈ ⨆ i, p i) ↔ (∀ N, (∀ i, p i ≤ N) → m ∈ N) :=
begin
  rw [← span_singleton_le_iff_mem, le_supr_iff],
  simp only [span_singleton_le_iff_mem],
end

end add_comm_monoid

end submodule
