/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Separation properties of topological spaces.
-/
import topology.subset_properties

open set filter
open_locale topological_space filter
local attribute [instance] classical.prop_decidable -- TODO: use "open_locale classical"

universes u v
variables {α : Type u} {β : Type v} [topological_space α]

section separation

/-- A T₀ space, also known as a Kolmogorov space, is a topological space
  where for every pair `x ≠ y`, there is an open set containing one but not the other. -/
class t0_space (α : Type u) [topological_space α] : Prop :=
(t0 : ∀ x y, x ≠ y → ∃ U:set α, is_open U ∧ (xor (x ∈ U) (y ∈ U)))

theorem exists_open_singleton_of_open_finset [t0_space α] (s : finset α) (sne : s.nonempty)
  (hso : is_open (↑s : set α)) :
  ∃ x ∈ s, is_open ({x} : set α):=
begin
  induction s using finset.strong_induction_on with s ihs,
  by_cases hs : set.subsingleton (↑s : set α),
  { rcases sne with ⟨x, hx⟩,
    refine ⟨x, hx, _⟩,
    have : (↑s : set α) = {x}, from hs.eq_singleton_of_mem hx,
    rwa this at hso },
  { dunfold set.subsingleton at hs,
    push_neg at hs,
    rcases hs with ⟨x, hx, y, hy, hxy⟩,
    rcases t0_space.t0 x y hxy with ⟨U, hU, hxyU⟩,
    wlog H : x ∈ U ∧ y ∉ U := hxyU using [x y, y x],
    obtain ⟨z, hzs, hz⟩ : ∃ z ∈ s.filter (λ z, z ∈ U), is_open ({z} : set α),
    { refine ihs _ (finset.filter_ssubset.2 ⟨y, hy, H.2⟩) ⟨x, finset.mem_filter.2 ⟨hx, H.1⟩⟩ _,
      rw [finset.coe_filter],
      exact is_open_inter hso hU },
    exact ⟨z, (finset.mem_filter.1 hzs).1, hz⟩ }
end

theorem exists_open_singleton_of_fintype [t0_space α] [f : fintype α] [ha : nonempty α] :
  ∃ x:α, is_open ({x}:set α) :=
begin
  refine ha.elim (λ x, _),
  have : is_open (↑(finset.univ : finset α) : set α), { simp },
  rcases exists_open_singleton_of_open_finset _ ⟨x, finset.mem_univ x⟩ this with ⟨x, _, hx⟩,
  exact ⟨x, hx⟩
end

instance subtype.t0_space [t0_space α] {p : α → Prop} : t0_space (subtype p) :=
⟨λ x y hxy, let ⟨U, hU, hxyU⟩ := t0_space.t0 (x:α) y ((not_congr subtype.ext_iff_val).1 hxy) in
  ⟨(coe : subtype p → α) ⁻¹' U, is_open_induced hU, hxyU⟩⟩

/-- A T₁ space, also known as a Fréchet space, is a topological space
  where every singleton set is closed. Equivalently, for every pair
  `x ≠ y`, there is an open set containing `x` and not `y`. -/
class t1_space (α : Type u) [topological_space α] : Prop :=
(t1 : ∀x, is_closed ({x} : set α))

lemma is_closed_singleton [t1_space α] {x : α} : is_closed ({x} : set α) :=
t1_space.t1 x

lemma is_open_ne [t1_space α] {x : α} : is_open {y | y ≠ x} :=
compl_singleton_eq x ▸ is_open_compl_iff.2 (t1_space.t1 x)

instance subtype.t1_space {α : Type u} [topological_space α] [t1_space α] {p : α → Prop} :
  t1_space (subtype p) :=
⟨λ ⟨x, hx⟩, is_closed_induced_iff.2 $ ⟨{x}, is_closed_singleton, set.ext $ λ y,
  by simp [subtype.ext_iff_val]⟩⟩

@[priority 100] -- see Note [lower instance priority]
instance t1_space.t0_space [t1_space α] : t0_space α :=
⟨λ x y h, ⟨{z | z ≠ y}, is_open_ne, or.inl ⟨h, not_not_intro rfl⟩⟩⟩

lemma compl_singleton_mem_nhds [t1_space α] {x y : α} (h : y ≠ x) : {x}ᶜ ∈ 𝓝 y :=
mem_nhds_sets is_closed_singleton $ by rwa [mem_compl_eq, mem_singleton_iff]

@[simp] lemma closure_singleton [t1_space α] {a : α} :
  closure ({a} : set α) = {a} :=
is_closed_singleton.closure_eq

lemma is_closed_map_const {α β} [topological_space α] [topological_space β] [t1_space β] {y : β} :
  is_closed_map (function.const α y) :=
begin
  apply is_closed_map.of_nonempty, intros s hs h2s, simp_rw [h2s.image_const, is_closed_singleton]
end

/-- A T₂ space, also known as a Hausdorff space, is one in which for every
  `x ≠ y` there exists disjoint open sets around `x` and `y`. This is
  the most widely used of the separation axioms. -/
class t2_space (α : Type u) [topological_space α] : Prop :=
(t2 : ∀x y, x ≠ y → ∃u v : set α, is_open u ∧ is_open v ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅)

lemma t2_separation [t2_space α] {x y : α} (h : x ≠ y) :
  ∃u v : set α, is_open u ∧ is_open v ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅ :=
t2_space.t2 x y h

@[priority 100] -- see Note [lower instance priority]
instance t2_space.t1_space [t2_space α] : t1_space α :=
⟨λ x, is_open_iff_forall_mem_open.2 $ λ y hxy,
let ⟨u, v, hu, hv, hyu, hxv, huv⟩ := t2_separation (mt mem_singleton_of_eq hxy) in
⟨u, λ z hz1 hz2, (ext_iff.1 huv x).1 ⟨mem_singleton_iff.1 hz2 ▸ hz1, hxv⟩, hu, hyu⟩⟩

lemma eq_of_nhds_ne_bot [ht : t2_space α] {x y : α} (h : ne_bot (𝓝 x ⊓ 𝓝 y)) : x = y :=
classical.by_contradiction $ assume : x ≠ y,
let ⟨u, v, hu, hv, hx, hy, huv⟩ := t2_space.t2 x y this in
absurd huv $ (inf_ne_bot_iff.1 h (mem_nhds_sets hu hx) (mem_nhds_sets hv hy)).ne_empty

lemma t2_iff_nhds : t2_space α ↔ ∀ {x y : α}, ne_bot (𝓝 x ⊓ 𝓝 y) → x = y :=
⟨assume h, by exactI λ x y, eq_of_nhds_ne_bot,
 assume h, ⟨assume x y xy,
   have 𝓝 x ⊓ 𝓝 y = ⊥ := classical.by_contradiction (mt h xy),
   let ⟨u', hu', v', hv', u'v'⟩ := empty_in_sets_eq_bot.mpr this,
       ⟨u, uu', uo, hu⟩ := mem_nhds_sets_iff.mp hu',
       ⟨v, vv', vo, hv⟩ := mem_nhds_sets_iff.mp hv' in
   ⟨u, v, uo, vo, hu, hv, disjoint.eq_bot $ disjoint.mono uu' vv' u'v'⟩⟩⟩

lemma t2_iff_ultrafilter :
  t2_space α ↔ ∀ f {x y : α}, is_ultrafilter f → f ≤ 𝓝 x → f ≤ 𝓝 y → x = y :=
t2_iff_nhds.trans
  ⟨assume h f x y u fx fy, h $ u.1.mono (le_inf fx fy),
   assume h x y xy,
     let ⟨f, hf, uf⟩ := @@exists_ultrafilter _ xy in
     h f uf (le_trans hf inf_le_left) (le_trans hf inf_le_right)⟩

lemma is_closed_diagonal [t2_space α] : is_closed (diagonal α) :=
is_closed_iff_cluster_pt.mpr $ assume ⟨a₁, a₂⟩ h, eq_of_nhds_ne_bot $ assume : 𝓝 a₁ ⊓ 𝓝 a₂ = ⊥, h $
  let ⟨t₁, ht₁, t₂, ht₂, (h' : t₁ ∩ t₂ ⊆ ∅)⟩ :=
    by rw [←empty_in_sets_eq_bot, mem_inf_sets] at this; exact this in
  begin
    change t₁ ∈ 𝓝 a₁ at ht₁,
    change t₂ ∈ 𝓝 a₂ at ht₂,
    rw [nhds_prod_eq, ←empty_in_sets_eq_bot],
    apply filter.sets_of_superset,
    apply inter_mem_inf_sets (prod_mem_prod ht₁ ht₂) (mem_principal_sets.mpr (subset.refl _)),
    exact assume ⟨x₁, x₂⟩ ⟨⟨hx₁, hx₂⟩, (heq : x₁ = x₂)⟩,
      show false, from @h' x₁ ⟨hx₁, heq.symm ▸ hx₂⟩
  end

lemma t2_iff_is_closed_diagonal : t2_space α ↔ is_closed (diagonal α) :=
begin
  split,
  { introI h,
    exact is_closed_diagonal },
  { intro h,
    constructor,
    intros x y hxy,
    have : (x, y) ∈ (diagonal α)ᶜ, by rwa [mem_compl_iff],
    obtain ⟨t, t_sub, t_op, xyt⟩ : ∃ t ⊆ (diagonal α)ᶜ, is_open t ∧ (x, y) ∈ t :=
      is_open_iff_forall_mem_open.mp h _ this,
    rcases is_open_prod_iff.mp t_op x y xyt with ⟨U, V, U_op, V_op, xU, yV, H⟩,
    use [U, V, U_op, V_op, xU, yV],
    have := subset.trans H t_sub,
    rw eq_empty_iff_forall_not_mem,
    rintros z ⟨zU, zV⟩,
    have : ¬ (z, z) ∈ diagonal α := this (mk_mem_prod zU zV),
    exact this rfl },
end

@[simp] lemma nhds_eq_nhds_iff {a b : α} [t2_space α] : 𝓝 a = 𝓝 b ↔ a = b :=
⟨assume h, eq_of_nhds_ne_bot $ by rw [h, inf_idem]; exact nhds_ne_bot, assume h, h ▸ rfl⟩

@[simp] lemma nhds_le_nhds_iff {a b : α} [t2_space α] : 𝓝 a ≤ 𝓝 b ↔ a = b :=
⟨assume h, eq_of_nhds_ne_bot $ by rw [inf_of_le_left h]; exact nhds_ne_bot, assume h, h ▸ le_refl _⟩

lemma tendsto_nhds_unique [t2_space α] {f : β → α} {l : filter β} {a b : α}
  [ne_bot l] (ha : tendsto f l (𝓝 a)) (hb : tendsto f l (𝓝 b)) : a = b :=
eq_of_nhds_ne_bot $ ne_bot_of_le $ le_inf ha hb

lemma tendsto_nhds_unique' [t2_space α] {f : β → α} {l : filter β} {a b : α}
  (hl : ne_bot l) (ha : tendsto f l (𝓝 a)) (hb : tendsto f l (𝓝 b)) : a = b :=
eq_of_nhds_ne_bot $ ne_bot_of_le $ le_inf ha hb

section lim
variables [t2_space α] {f : filter α}

/-!
### Properties of `Lim` and `lim`

In this section we use explicit `nonempty α` instances for `Lim` and `lim`. This way the lemmas
are useful without a `nonempty α` instance.
-/

lemma Lim_eq {a : α} [ne_bot f] (h : f ≤ 𝓝 a) :
  @Lim _ _ ⟨a⟩ f = a :=
tendsto_nhds_unique (le_nhds_Lim ⟨a, h⟩) h

lemma Lim_eq_iff [ne_bot f] (h : ∃ (a : α), f ≤ nhds a) {a} : @Lim _ _ ⟨a⟩ f = a ↔ f ≤ 𝓝 a :=
⟨λ c, c ▸ le_nhds_Lim h, Lim_eq⟩

lemma is_ultrafilter.Lim_eq_iff_le_nhds [compact_space α] (x : α) (F : ultrafilter α) :
  @Lim _ _ ⟨x⟩ F.1 = x ↔ F.1 ≤ 𝓝 x :=
⟨λ h, h ▸ is_ultrafilter.le_nhds_Lim _, Lim_eq⟩

lemma is_open_iff_ultrafilter' [compact_space α] (U : set α) :
  is_open U ↔ (∀ F : ultrafilter α, F.Lim ∈ U → U ∈ F.1) :=
begin
  rw is_open_iff_ultrafilter,
  refine ⟨λ h F hF, h _ hF _ F.2 (is_ultrafilter.le_nhds_Lim _), _⟩,
  intros cond x hx f hf h,
  let F : ultrafilter α := ⟨f, hf⟩,
  change F.1 ≤ _ at h,
  rw ←is_ultrafilter.Lim_eq_iff_le_nhds at h,
  rw ←h at *,
  exact cond _ hx
end

lemma filter.tendsto.lim_eq {a : α} {f : filter β} [ne_bot f] {g : β → α} (h : tendsto g f (𝓝 a)) :
  @lim _ _ _ ⟨a⟩ f g = a :=
Lim_eq h

lemma filter.lim_eq_iff {f : filter β} [ne_bot f] {g : β → α} (h : ∃ a, tendsto g f (𝓝 a)) {a} :
  @lim _ _ _ ⟨a⟩ f g = a ↔ tendsto g f (𝓝 a) :=
⟨λ c, c ▸ tendsto_nhds_lim h, filter.tendsto.lim_eq⟩

lemma continuous.lim_eq [topological_space β] {f : β → α} (h : continuous f) (a : β) :
  @lim _ _ _ ⟨f a⟩ (𝓝 a) f = f a :=
(h.tendsto a).lim_eq

@[simp] lemma Lim_nhds (a : α) : @Lim _ _ ⟨a⟩ (𝓝 a) = a :=
Lim_eq (le_refl _)

@[simp] lemma lim_nhds_id (a : α) : @lim _ _ _ ⟨a⟩ (𝓝 a) id = a :=
Lim_nhds a

@[simp] lemma Lim_nhds_within {a : α} {s : set α} (h : a ∈ closure s) :
  @Lim _ _ ⟨a⟩ (𝓝[s] a) = a :=
by haveI : ne_bot (𝓝[s] a) := mem_closure_iff_cluster_pt.1 h;
exact Lim_eq inf_le_left

@[simp] lemma lim_nhds_within_id {a : α} {s : set α} (h : a ∈ closure s) :
  @lim _ _ _ ⟨a⟩ (𝓝[s] a) id = a :=
Lim_nhds_within h

end lim

@[priority 100] -- see Note [lower instance priority]
instance t2_space_discrete {α : Type*} [topological_space α] [discrete_topology α] : t2_space α :=
{ t2 := assume x y hxy, ⟨{x}, {y}, is_open_discrete _, is_open_discrete _, rfl, rfl,
  eq_empty_iff_forall_not_mem.2 $ by intros z hz;
    cases eq_of_mem_singleton hz.1; cases eq_of_mem_singleton hz.2; cc⟩ }

private lemma separated_by_f {α : Type*} {β : Type*}
  [tα : topological_space α] [tβ : topological_space β] [t2_space β]
  (f : α → β) (hf : tα ≤ tβ.induced f) {x y : α} (h : f x ≠ f y) :
  ∃u v : set α, is_open u ∧ is_open v ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅ :=
let ⟨u, v, uo, vo, xu, yv, uv⟩ := t2_separation h in
⟨f ⁻¹' u, f ⁻¹' v, hf _ ⟨u, uo, rfl⟩, hf _ ⟨v, vo, rfl⟩, xu, yv,
  by rw [←preimage_inter, uv, preimage_empty]⟩

instance {α : Type*} {p : α → Prop} [t : topological_space α] [t2_space α] : t2_space (subtype p) :=
⟨assume x y h,
  separated_by_f subtype.val (le_refl _) (mt subtype.eq h)⟩

instance {α : Type*} {β : Type*} [t₁ : topological_space α] [t2_space α]
  [t₂ : topological_space β] [t2_space β] : t2_space (α × β) :=
⟨assume ⟨x₁,x₂⟩ ⟨y₁,y₂⟩ h,
  or.elim (not_and_distrib.mp (mt prod.ext_iff.mpr h))
    (λ h₁, separated_by_f prod.fst inf_le_left h₁)
    (λ h₂, separated_by_f prod.snd inf_le_right h₂)⟩

instance Pi.t2_space {α : Type*} {β : α → Type v} [t₂ : Πa, topological_space (β a)] [Πa, t2_space (β a)] :
  t2_space (Πa, β a) :=
⟨assume x y h,
  let ⟨i, hi⟩ := not_forall.mp (mt funext h) in
  separated_by_f (λz, z i) (infi_le _ i) hi⟩

variables [topological_space β]

lemma is_closed_eq [t2_space α] {f g : β → α}
  (hf : continuous f) (hg : continuous g) : is_closed {x:β | f x = g x} :=
continuous_iff_is_closed.mp (hf.prod_mk hg) _ is_closed_diagonal

/-- If two continuous maps are equal on `s`, then they are equal on the closure of `s`. -/
lemma set.eq_on.closure [t2_space α] {s : set β} {f g : β → α} (h : eq_on f g s)
  (hf : continuous f) (hg : continuous g) :
  eq_on f g (closure s) :=
closure_minimal h (is_closed_eq hf hg)

/-- If two continuous functions are equal on a dense set, then they are equal. -/
lemma continuous.ext_on [t2_space α] {s : set β} (hs : dense s) {f g : β → α}
  (hf : continuous f) (hg : continuous g) (h : eq_on f g s) :
  f = g :=
funext $ λ x, h.closure hf hg (hs x)

lemma diagonal_eq_range_diagonal_map {α : Type*} : {p:α×α | p.1 = p.2} = range (λx, (x,x)) :=
ext $ assume p, iff.intro
  (assume h, ⟨p.1, prod.ext_iff.2 ⟨rfl, h⟩⟩)
  (assume ⟨x, hx⟩, show p.1 = p.2, by rw ←hx)

lemma prod_subset_compl_diagonal_iff_disjoint {α : Type*} {s t : set α} :
  set.prod s t ⊆ {p:α×α | p.1 = p.2}ᶜ ↔ s ∩ t = ∅ :=
by rw [eq_empty_iff_forall_not_mem, subset_compl_comm,
       diagonal_eq_range_diagonal_map, range_subset_iff]; simp

lemma compact_compact_separated [t2_space α] {s t : set α}
  (hs : is_compact s) (ht : is_compact t) (hst : s ∩ t = ∅) :
  ∃u v : set α, is_open u ∧ is_open v ∧ s ⊆ u ∧ t ⊆ v ∧ u ∩ v = ∅ :=
by simp only [prod_subset_compl_diagonal_iff_disjoint.symm] at ⊢ hst;
   exact generalized_tube_lemma hs ht is_closed_diagonal hst

lemma is_compact.is_closed [t2_space α] {s : set α} (hs : is_compact s) : is_closed s :=
is_open_compl_iff.mpr $ is_open_iff_forall_mem_open.mpr $ assume x hx,
  let ⟨u, v, uo, vo, su, xv, uv⟩ :=
    compact_compact_separated hs (compact_singleton : is_compact {x})
      (by rwa [inter_comm, ←subset_compl_iff_disjoint, singleton_subset_iff]) in
  have v ⊆ sᶜ, from
    subset_compl_comm.mp (subset.trans su (subset_compl_iff_disjoint.mpr uv)),
⟨v, this, vo, by simpa using xv⟩

lemma is_compact.inter [t2_space α] {s t : set α} (hs : is_compact s) (ht : is_compact t) :
  is_compact (s ∩ t) :=
hs.inter_right $ ht.is_closed

/-- If a compact set is covered by two open sets, then we can cover it by two compact subsets. -/
lemma is_compact.binary_compact_cover [t2_space α] {K U V : set α} (hK : is_compact K)
  (hU : is_open U) (hV : is_open V) (h2K : K ⊆ U ∪ V) :
  ∃ K₁ K₂ : set α, is_compact K₁ ∧ is_compact K₂ ∧ K₁ ⊆ U ∧ K₂ ⊆ V ∧ K = K₁ ∪ K₂ :=
begin
  rcases compact_compact_separated (compact_diff hK hU) (compact_diff hK hV)
    (by rwa [diff_inter_diff, diff_eq_empty]) with ⟨O₁, O₂, h1O₁, h1O₂, h2O₁, h2O₂, hO⟩,
  refine ⟨_, _, compact_diff hK h1O₁, compact_diff hK h1O₂,
    by rwa [diff_subset_comm], by rwa [diff_subset_comm], by rw [← diff_inter, hO, diff_empty]⟩
end

section
open finset function
/-- For every finite open cover `Uᵢ` of a compact set, there exists a compact cover `Kᵢ ⊆ Uᵢ`. -/
lemma is_compact.finite_compact_cover [t2_space α] {s : set α} (hs : is_compact s) {ι} (t : finset ι)
  (U : ι → set α) (hU : ∀ i ∈ t, is_open (U i)) (hsC : s ⊆ ⋃ i ∈ t, U i) :
  ∃ K : ι → set α, (∀ i, is_compact (K i)) ∧ (∀i, K i ⊆ U i) ∧ s = ⋃ i ∈ t, K i :=
begin
  classical,
  induction t using finset.induction with x t hx ih generalizing U hU s hs hsC,
  { refine ⟨λ _, ∅, λ i, compact_empty, λ i, empty_subset _, _⟩, simpa only [subset_empty_iff,
      finset.not_mem_empty, Union_neg, Union_empty, not_false_iff] using hsC },
  simp only [finset.bUnion_insert] at hsC,
  simp only [finset.mem_insert] at hU,
  have hU' : ∀ i ∈ t, is_open (U i) := λ i hi, hU i (or.inr hi),
  rcases hs.binary_compact_cover (hU x (or.inl rfl)) (is_open_bUnion hU') hsC
    with ⟨K₁, K₂, h1K₁, h1K₂, h2K₁, h2K₂, hK⟩,
  rcases ih U hU' h1K₂ h2K₂ with ⟨K, h1K, h2K, h3K⟩,
  refine ⟨update K x K₁, _, _, _⟩,
  { intros i, by_cases hi : i = x,
    { simp only [update_same, hi, h1K₁] },
    { rw [← ne.def] at hi, simp only [update_noteq hi, h1K] }},
  { intros i, by_cases hi : i = x,
    { simp only [update_same, hi, h2K₁] },
    { rw [← ne.def] at hi, simp only [update_noteq hi, h2K] }},
  { simp only [bUnion_insert_update _ hx, hK, h3K] }
end
end

lemma locally_compact_of_compact_nhds [t2_space α] (h : ∀ x : α, ∃ s, s ∈ 𝓝 x ∧ is_compact s) :
  locally_compact_space α :=
⟨assume x n hn,
  let ⟨u, un, uo, xu⟩ := mem_nhds_sets_iff.mp hn in
  let ⟨k, kx, kc⟩ := h x in
  -- K is compact but not necessarily contained in N.
  -- K \ U is again compact and doesn't contain x, so
  -- we may find open sets V, W separating x from K \ U.
  -- Then K \ W is a compact neighborhood of x contained in U.
  let ⟨v, w, vo, wo, xv, kuw, vw⟩ :=
    compact_compact_separated compact_singleton (compact_diff kc uo)
      (by rw [singleton_inter_eq_empty]; exact λ h, h.2 xu) in
  have wn : wᶜ ∈ 𝓝 x, from
   mem_nhds_sets_iff.mpr
     ⟨v, subset_compl_iff_disjoint.mpr vw, vo, singleton_subset_iff.mp xv⟩,
  ⟨k \ w,
   filter.inter_mem_sets kx wn,
   subset.trans (diff_subset_comm.mp kuw) un,
   compact_diff kc wo⟩⟩

@[priority 100] -- see Note [lower instance priority]
instance locally_compact_of_compact [t2_space α] [compact_space α] : locally_compact_space α :=
locally_compact_of_compact_nhds (assume x, ⟨univ, mem_nhds_sets is_open_univ trivial, compact_univ⟩)

/-- In a locally compact T₂ space, every point has an open neighborhood with compact closure -/
lemma exists_open_with_compact_closure [locally_compact_space α] [t2_space α] (x : α) :
  ∃ (U : set α), is_open U ∧ x ∈ U ∧ is_compact (closure U) :=
begin
  rcases locally_compact_space.local_compact_nhds x set.univ filter.univ_mem_sets with
    ⟨K, h1K, _, h2K⟩,
  rw [mem_nhds_sets_iff] at h1K, rcases h1K with ⟨t, h1t, h2t, h3t⟩,
  exact ⟨t, h2t, h3t, compact_of_is_closed_subset h2K is_closed_closure $
    closure_minimal h1t $ h2K.is_closed⟩
end

/-- In a locally compact T₂ space, every compact set is contained in the interior of a compact
  set. -/
lemma exists_compact_superset [locally_compact_space α] [t2_space α] {K : set α}
  (hK : is_compact K) : ∃ (K' : set α), is_compact K' ∧ K ⊆ interior K' :=
begin
  choose U hU using λ x : K, exists_open_with_compact_closure (x : α),
  rcases hK.elim_finite_subcover U (λ x, (hU x).1) (λ x hx, ⟨_, ⟨⟨x, hx⟩, rfl⟩, (hU ⟨x, hx⟩).2.1⟩) with
    ⟨s, hs⟩,
  refine ⟨⋃ (i : K) (H : i ∈ s), closure (U i), _, _⟩,
  exact (finite_mem_finset s).compact_bUnion (λ x hx, (hU x).2.2),
  refine subset.trans hs _, rw subset_interior_iff_subset_of_open,
  exact bUnion_subset_bUnion_right (λ x hx, subset_closure),
  exact is_open_bUnion (λ x hx, (hU x).1)
end

end separation

section regularity

/-- A T₃ space, also known as a regular space (although this condition sometimes
  omits T₂), is one in which for every closed `C` and `x ∉ C`, there exist
  disjoint open sets containing `x` and `C` respectively. -/
class regular_space (α : Type u) [topological_space α] extends t1_space α : Prop :=
(regular : ∀{s:set α} {a}, is_closed s → a ∉ s → ∃t, is_open t ∧ s ⊆ t ∧ 𝓝[t] a = ⊥)

lemma nhds_is_closed [regular_space α] {a : α} {s : set α} (h : s ∈ 𝓝 a) :
  ∃t∈(𝓝 a), t ⊆ s ∧ is_closed t :=
let ⟨s', h₁, h₂, h₃⟩ := mem_nhds_sets_iff.mp h in
have ∃t, is_open t ∧ s'ᶜ ⊆ t ∧ 𝓝[t] a = ⊥,
  from regular_space.regular (is_closed_compl_iff.mpr h₂) (not_not_intro h₃),
let ⟨t, ht₁, ht₂, ht₃⟩ := this in
⟨tᶜ,
  mem_sets_of_eq_bot $ by rwa [compl_compl],
  subset.trans (compl_subset_comm.1 ht₂) h₁,
  is_closed_compl_iff.mpr ht₁⟩

lemma closed_nhds_basis [regular_space α] (a : α) :
  (𝓝 a).has_basis (λ s : set α, s ∈ 𝓝 a ∧ is_closed s) id :=
⟨λ t, ⟨λ t_in, let ⟨s, s_in, h_st, h⟩ := nhds_is_closed t_in in ⟨s, ⟨s_in, h⟩, h_st⟩,
       λ ⟨s, ⟨s_in, hs⟩, hst⟩, mem_sets_of_superset s_in hst⟩⟩

instance subtype.regular_space [regular_space α] {p : α → Prop} : regular_space (subtype p) :=
⟨begin
   intros s a hs ha,
   rcases is_closed_induced_iff.1 hs with ⟨s, hs', rfl⟩,
   rcases regular_space.regular hs' ha with ⟨t, ht, hst, hat⟩,
   refine ⟨coe ⁻¹' t, is_open_induced ht, preimage_mono hst, _⟩,
   rw [nhds_within, nhds_induced, ← comap_principal, ← comap_inf, ← nhds_within, hat, comap_bot]
 end⟩

variable (α)
@[priority 100] -- see Note [lower instance priority]
instance regular_space.t2_space [regular_space α] : t2_space α :=
⟨λ x y hxy,
let ⟨s, hs, hys, hxs⟩ := regular_space.regular is_closed_singleton
    (mt mem_singleton_iff.1 hxy),
  ⟨t, hxt, u, hsu, htu⟩ := empty_in_sets_eq_bot.2 hxs,
  ⟨v, hvt, hv, hxv⟩ := mem_nhds_sets_iff.1 hxt in
⟨v, s, hv, hs, hxv, singleton_subset_iff.1 hys,
eq_empty_of_subset_empty $ λ z ⟨hzv, hzs⟩, htu ⟨hvt hzv, hsu hzs⟩⟩⟩

variable {α}

lemma disjoint_nested_nhds [regular_space α] {x y : α} (h : x ≠ y) :
  ∃ (U₁ V₁ ∈ 𝓝 x) (U₂ V₂ ∈ 𝓝 y), is_closed V₁ ∧ is_closed V₂ ∧ is_open U₁ ∧ is_open U₂ ∧
  V₁ ⊆ U₁ ∧ V₂ ⊆ U₂ ∧ U₁ ∩ U₂ = ∅ :=
begin
  rcases t2_separation h with ⟨U₁, U₂, U₁_op, U₂_op, x_in, y_in, H⟩,
  rcases nhds_is_closed (mem_nhds_sets U₁_op x_in) with ⟨V₁, V₁_in, h₁, V₁_closed⟩,
  rcases nhds_is_closed (mem_nhds_sets U₂_op y_in) with ⟨V₂, V₂_in, h₂, V₂_closed⟩,
  use [U₁, V₁, mem_sets_of_superset V₁_in h₁, V₁_in,
       U₂, V₂, mem_sets_of_superset V₂_in h₂, V₂_in],
  tauto
end

end regularity

section normality

/-- A T₄ space, also known as a normal space (although this condition sometimes
  omits T₂), is one in which for every pair of disjoint closed sets `C` and `D`,
  there exist disjoint open sets containing `C` and `D` respectively. -/
class normal_space (α : Type u) [topological_space α] extends t1_space α : Prop :=
(normal : ∀ s t : set α, is_closed s → is_closed t → disjoint s t →
  ∃ u v, is_open u ∧ is_open v ∧ s ⊆ u ∧ t ⊆ v ∧ disjoint u v)

theorem normal_separation [normal_space α] (s t : set α)
  (H1 : is_closed s) (H2 : is_closed t) (H3 : disjoint s t) :
  ∃ u v, is_open u ∧ is_open v ∧ s ⊆ u ∧ t ⊆ v ∧ disjoint u v :=
normal_space.normal s t H1 H2 H3

@[priority 100] -- see Note [lower instance priority]
instance normal_space.regular_space [normal_space α] : regular_space α :=
{ regular := λ s x hs hxs, let ⟨u, v, hu, hv, hsu, hxv, huv⟩ := normal_separation s {x} hs is_closed_singleton
      (λ _ ⟨hx, hy⟩, hxs $ set.mem_of_eq_of_mem (set.eq_of_mem_singleton hy).symm hx) in
    ⟨u, hu, hsu, filter.empty_in_sets_eq_bot.1 $ filter.mem_inf_sets.2
      ⟨v, mem_nhds_sets hv (set.singleton_subset_iff.1 hxv), u, filter.mem_principal_self u, set.inter_comm u v ▸ huv⟩⟩ }

-- We can't make this an instance because it could cause an instance loop.
lemma normal_of_compact_t2 [compact_space α] [t2_space α] : normal_space α :=
begin
  refine ⟨assume s t hs ht st, _⟩,
  simp only [disjoint_iff],
  exact compact_compact_separated hs.compact ht.compact st.eq_bot
end

end normality
