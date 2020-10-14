/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Bases of topologies. Countability axioms.
-/
import topology.continuous_on

open set filter classical
open_locale topological_space filter
noncomputable theory

namespace topological_space
/- countability axioms

For our applications we are interested that there exists a countable basis, but we do not need the
concrete basis itself. This allows us to declare these type classes as `Prop` to use them as mixins.
-/
universe u
variables {α : Type u} [t : topological_space α]
include t

/-- A topological basis is one that satisfies the necessary conditions so that
  it suffices to take unions of the basis sets to get a topology (without taking
  finite intersections as well). -/
def is_topological_basis (s : set (set α)) : Prop :=
(∀t₁∈s, ∀t₂∈s, ∀ x ∈ t₁ ∩ t₂, ∃ t₃∈s, x ∈ t₃ ∧ t₃ ⊆ t₁ ∩ t₂) ∧
(⋃₀ s) = univ ∧
t = generate_from s

lemma is_topological_basis_of_subbasis {s : set (set α)} (hs : t = generate_from s) :
  is_topological_basis ((λf, ⋂₀ f) '' {f:set (set α) | finite f ∧ f ⊆ s ∧ (⋂₀ f).nonempty}) :=
let b' := (λf, ⋂₀ f) '' {f:set (set α) | finite f ∧ f ⊆ s ∧ (⋂₀ f).nonempty} in
⟨assume s₁ ⟨t₁, ⟨hft₁, ht₁b, ht₁⟩, eq₁⟩ s₂ ⟨t₂, ⟨hft₂, ht₂b, ht₂⟩, eq₂⟩,
    have ie : ⋂₀(t₁ ∪ t₂) = ⋂₀ t₁ ∩ ⋂₀ t₂, from Inf_union,
    eq₁ ▸ eq₂ ▸ assume x h,
      ⟨_, ⟨t₁ ∪ t₂, ⟨hft₁.union hft₂, union_subset ht₁b ht₂b,
        ie.symm ▸ ⟨_, h⟩⟩, ie⟩, h, subset.refl _⟩,
  eq_univ_iff_forall.2 $ assume a, ⟨univ, ⟨∅, ⟨finite_empty, empty_subset _,
    by rw sInter_empty; exact ⟨a, mem_univ a⟩⟩, sInter_empty⟩, mem_univ _⟩,
 have generate_from s = generate_from b',
    from le_antisymm
      (le_generate_from $ assume u ⟨t, ⟨hft, htb, ne⟩, eq⟩,
        eq ▸ @is_open_sInter _ (generate_from s) _ hft (assume s hs, generate_open.basic _ $ htb hs))
      (le_generate_from $ assume s hs,
        s.eq_empty_or_nonempty.elim
          (assume : s = ∅, by rw [this]; apply @is_open_empty _ _)
          (assume : s.nonempty, generate_open.basic _ ⟨{s}, ⟨finite_singleton s, singleton_subset_iff.2 hs,
            by rwa sInter_singleton⟩, sInter_singleton s⟩)),
  this ▸ hs⟩

lemma is_topological_basis_of_open_of_nhds {s : set (set α)}
  (h_open : ∀ u ∈ s, is_open u)
  (h_nhds : ∀(a:α) (u : set α), a ∈ u → is_open u → ∃v ∈ s, a ∈ v ∧ v ⊆ u) :
  is_topological_basis s :=
⟨assume t₁ ht₁ t₂ ht₂ x ⟨xt₁, xt₂⟩,
    h_nhds x (t₁ ∩ t₂) ⟨xt₁, xt₂⟩
      (is_open_inter (h_open _ ht₁) (h_open _ ht₂)),
  eq_univ_iff_forall.2 $ assume a,
    let ⟨u, h₁, h₂, _⟩ := h_nhds a univ trivial is_open_univ in
    ⟨u, h₁, h₂⟩,
  le_antisymm
    (le_generate_from h_open)
    (assume u hu,
      (@is_open_iff_nhds α (generate_from _) _).mpr $ assume a hau,
        let ⟨v, hvs, hav, hvu⟩ := h_nhds a u hau hu in
        by rw nhds_generate_from; exact infi_le_of_le v (infi_le_of_le ⟨hav, hvs⟩ $ le_principal_iff.2 hvu))⟩

lemma mem_nhds_of_is_topological_basis {a : α} {s : set α} {b : set (set α)}
  (hb : is_topological_basis b) : s ∈ 𝓝 a ↔ ∃t∈b, a ∈ t ∧ t ⊆ s :=
begin
  change s ∈ (𝓝 a).sets ↔ ∃t∈b, a ∈ t ∧ t ⊆ s,
  rw [hb.2.2, nhds_generate_from, binfi_sets_eq],
  { simp only [mem_bUnion_iff, exists_prop, mem_set_of_eq, and_assoc, and.left_comm], refl },
  { exact assume s ⟨hs₁, hs₂⟩ t ⟨ht₁, ht₂⟩,
      have a ∈ s ∩ t, from ⟨hs₁, ht₁⟩,
      let ⟨u, hu₁, hu₂, hu₃⟩ := hb.1 _ hs₂ _ ht₂ _ this in
      ⟨u, ⟨hu₂, hu₁⟩, le_principal_iff.2 (subset.trans hu₃ (inter_subset_left _ _)),
        le_principal_iff.2 (subset.trans hu₃ (inter_subset_right _ _))⟩ },
  { rcases eq_univ_iff_forall.1 hb.2.1 a with ⟨i, h1, h2⟩,
    exact ⟨i, h2, h1⟩ }
end

lemma is_open_of_is_topological_basis {s : set α} {b : set (set α)}
  (hb : is_topological_basis b) (hs : s ∈ b) : is_open s :=
is_open_iff_mem_nhds.2 $ λ a as,
(mem_nhds_of_is_topological_basis hb).2 ⟨s, hs, as, subset.refl _⟩

lemma mem_basis_subset_of_mem_open {b : set (set α)}
  (hb : is_topological_basis b) {a:α} {u : set α} (au : a ∈ u)
  (ou : is_open u) : ∃v ∈ b, a ∈ v ∧ v ⊆ u :=
(mem_nhds_of_is_topological_basis hb).1 $ mem_nhds_sets ou au

lemma sUnion_basis_of_is_open {B : set (set α)}
  (hB : is_topological_basis B) {u : set α} (ou : is_open u) :
  ∃ S ⊆ B, u = ⋃₀ S :=
⟨{s ∈ B | s ⊆ u}, λ s h, h.1, set.ext $ λ a,
  ⟨λ ha, let ⟨b, hb, ab, bu⟩ := mem_basis_subset_of_mem_open hB ha ou in
         ⟨b, ⟨hb, bu⟩, ab⟩,
   λ ⟨b, ⟨hb, bu⟩, ab⟩, bu ab⟩⟩

lemma Union_basis_of_is_open {B : set (set α)}
  (hB : is_topological_basis B) {u : set α} (ou : is_open u) :
  ∃ (β : Type u) (f : β → set α), u = (⋃ i, f i) ∧ ∀ i, f i ∈ B :=
let ⟨S, sb, su⟩ := sUnion_basis_of_is_open hB ou in
⟨S, subtype.val, su.trans set.sUnion_eq_Union, λ ⟨b, h⟩, sb h⟩

variables (α)

/-- A separable space is one with a countable dense subset, available through
`topological_space.exists_countable_dense`. If `α` is also known to be nonempty, then
`topological_space.dense_seq` provides a sequence `ℕ → α` with dense range, see
`topological_space.dense_range_dense_seq`.

If `α` is a uniform space with countably generated uniformity filter (e.g., an `emetric_space`),
then this condition is equivalent to `topological_space.second_countable_topology α`. In this case
the latter should be used as a typeclass argument in theorems because Lean can automatically deduce
`separable_space` from `second_countable_topology` but it can't deduce `second_countable_topology`
and `emetric_space`. -/
class separable_space : Prop :=
(exists_countable_dense : ∃s:set α, countable s ∧ dense s)

lemma exists_countable_dense [separable_space α] :
  ∃ s : set α, countable s ∧ dense s :=
separable_space.exists_countable_dense

/-- A nonempty separable space admits a sequence with dense range. Instead of running `cases` on the
conclusion of this lemma, you might want to use `topological_space.dense_seq` and
`topological_space.dense_range_dense_seq`.

If `α` might be empty, then `exists_countable_dense` is the main way to use separability of `α`. -/
lemma exists_dense_seq [separable_space α] [nonempty α] : ∃ u : ℕ → α, dense_range u :=
begin
  obtain ⟨s : set α, hs, s_dense⟩ := exists_countable_dense α,
  cases countable_iff_exists_surjective.mp hs with u hu,
  exact ⟨u, s_dense.mono hu⟩,
end

/-- A sequence dense in a non-empty separable topological space.

If `α` might be empty, then `exists_countable_dense` is the main way to use separability of `α`. -/
def dense_seq [separable_space α] [nonempty α] : ℕ → α := classical.some (exists_dense_seq α)

/-- The sequence `dense_seq α` has dense range. -/
@[simp] lemma dense_range_dense_seq [separable_space α] [nonempty α] :
  dense_range (dense_seq α) := classical.some_spec (exists_dense_seq α)

end topological_space

open topological_space

/-- If `α` is a separable space and `f : α → β` is a continuous map with dense range, then `β` is
a separable space as well. E.g., the completion of a separable uniform space is separable. -/
protected lemma dense_range.separable_space {α β : Type*} [topological_space α] [separable_space α]
  [topological_space β] {f : α → β} (h : dense_range f) (h' : continuous f) :
  separable_space β :=
let ⟨s, s_cnt, s_dense⟩ := exists_countable_dense α in
⟨⟨f '' s, countable.image s_cnt f, h.dense_image h' s_dense⟩⟩

namespace topological_space
universe u
variables (α : Type u) [t : topological_space α]
include t


/-- A first-countable space is one in which every point has a
  countable neighborhood basis. -/
class first_countable_topology : Prop :=
(nhds_generated_countable : ∀a:α, (𝓝 a).is_countably_generated)

namespace first_countable_topology
variable {α}

lemma tendsto_subseq [first_countable_topology α] {u : ℕ → α} {x : α} (hx : map_cluster_pt x at_top u) :
  ∃ (ψ : ℕ → ℕ), (strict_mono ψ) ∧ (tendsto (u ∘ ψ) at_top (𝓝 x)) :=
(nhds_generated_countable x).subseq_tendsto hx

end first_countable_topology

variables {α}

lemma is_countably_generated_nhds [first_countable_topology α] (x : α) :
  is_countably_generated (𝓝 x) :=
first_countable_topology.nhds_generated_countable x

lemma is_countably_generated_nhds_within [first_countable_topology α] (x : α) (s : set α) :
  is_countably_generated (𝓝[s] x) :=
(is_countably_generated_nhds x).inf_principal s

variable (α)

/-- A second-countable space is one with a countable basis. -/
class second_countable_topology : Prop :=
(is_open_generated_countable [] : ∃b:set (set α), countable b ∧ t = topological_space.generate_from b)

@[priority 100] -- see Note [lower instance priority]
instance second_countable_topology.to_first_countable_topology
  [second_countable_topology α] : first_countable_topology α :=
let ⟨b, hb, eq⟩ := second_countable_topology.is_open_generated_countable α in
⟨begin
   intros,
   rw [eq, nhds_generate_from],
   exact is_countably_generated_binfi_principal (hb.mono (assume x, and.right)),
 end⟩

lemma second_countable_topology_induced (β)
  [t : topological_space β] [second_countable_topology β] (f : α → β) :
  @second_countable_topology α (t.induced f) :=
begin
  rcases second_countable_topology.is_open_generated_countable β with ⟨b, hb, eq⟩,
  refine { is_open_generated_countable := ⟨preimage f '' b, hb.image _, _⟩ },
  rw [eq, induced_generate_from_eq]
end

instance subtype.second_countable_topology
  (s : set α) [second_countable_topology α] : second_countable_topology s :=
second_countable_topology_induced s α coe

lemma is_open_generated_countable_inter [second_countable_topology α] :
  ∃b:set (set α), countable b ∧ ∅ ∉ b ∧ is_topological_basis b :=
let ⟨b, hb₁, hb₂⟩ := second_countable_topology.is_open_generated_countable α in
let b' := (λs, ⋂₀ s) '' {s:set (set α) | finite s ∧ s ⊆ b ∧ (⋂₀ s).nonempty} in
⟨b',
  ((countable_set_of_finite_subset hb₁).mono
    (by { simp only [← and_assoc], apply inter_subset_left })).image _,
  assume ⟨s, ⟨_, _, hn⟩, hp⟩, absurd hn (not_nonempty_iff_eq_empty.2 hp),
  is_topological_basis_of_subbasis hb₂⟩

/- TODO: more fine grained instances for first_countable_topology, separable_space, t2_space, ... -/
instance {β : Type*} [topological_space β]
  [second_countable_topology α] [second_countable_topology β] : second_countable_topology (α × β) :=
⟨let ⟨a, ha₁, ha₂, ha₃, ha₄, ha₅⟩ := is_open_generated_countable_inter α in
  let ⟨b, hb₁, hb₂, hb₃, hb₄, hb₅⟩ := is_open_generated_countable_inter β in
  ⟨{g | ∃u∈a, ∃v∈b, g = set.prod u v},
    have {g | ∃u∈a, ∃v∈b, g = set.prod u v} = (⋃u∈a, ⋃v∈b, {set.prod u v}),
      by apply set.ext; simp,
    by rw [this]; exact (ha₁.bUnion $ assume u hu, hb₁.bUnion $ by simp),
    by rw [ha₅, hb₅, prod_generate_from_generate_from_eq ha₄ hb₄]⟩⟩

instance second_countable_topology_fintype {ι : Type*} {π : ι → Type*}
  [fintype ι] [t : ∀a, topological_space (π a)] [sc : ∀a, second_countable_topology (π a)] :
  second_countable_topology (∀a, π a) :=
have ∀i, ∃b : set (set (π i)), countable b ∧ ∅ ∉ b ∧ is_topological_basis b, from
  assume a, @is_open_generated_countable_inter (π a) _ (sc a),
let ⟨g, hg⟩ := classical.axiom_of_choice this in
have t = (λa, generate_from (g a)), from funext $ assume a, (hg a).2.2.2.2,
begin
  constructor,
  refine ⟨pi univ '' pi univ g, countable.image _ _, _⟩,
  { suffices : countable {f : Πa, set (π a) | ∀a, f a ∈ g a}, { simpa [pi] },
    exact countable_pi (assume i, (hg i).1), },
  rw [this, pi_generate_from_eq_fintype],
  { congr' 1 with f, simp [pi, eq_comm] },
  exact assume a, (hg a).2.2.2.1
end

@[priority 100] -- see Note [lower instance priority]
instance second_countable_topology.to_separable_space
  [second_countable_topology α] : separable_space α :=
begin
  rcases is_open_generated_countable_inter α with  ⟨b, hbc, hbne, hb, hbU, eq⟩,
  set S : α → set (set α) := λ a, {s : set α | a ∈ s ∧ s ∈ b},
  have nhds_eq : ∀a, 𝓝 a = (⨅ s ∈ S a, 𝓟 s),
  { intro a, rw [eq, nhds_generate_from] },
  have : ∀ s ∈ b, set.nonempty s :=
    assume s hs, ne_empty_iff_nonempty.1 $ λ eq, absurd hs (eq.symm ▸ hbne),
  choose f hf,
  refine ⟨⟨⋃ s ∈ b, {f s ‹_›}, hbc.bUnion (λ _ _, countable_singleton _), λ a, _⟩⟩,
  suffices : (⨅ s ∈ S a, 𝓟 (s ∩ ⋃ t ∈ b, {f t ‹_›})).ne_bot,
  { obtain ⟨t, htb, hta⟩ : a ∈ ⋃₀ b, { simp only [hbU] },
    have A : ∃ s, s ∈ S a := ⟨t, hta, htb⟩,
    simpa only [← inf_principal, mem_closure_iff_cluster_pt,
      cluster_pt, nhds_eq, binfi_inf A] using this },
  rw [infi_subtype'],
  haveI : nonempty α := ⟨a⟩,
  refine infi_ne_bot_of_directed _ _,
  { rintros ⟨s₁, has₁, hs₁⟩ ⟨s₂, has₂, hs₂⟩,
    obtain ⟨t, htb, hta, ht⟩ : ∃ t ∈ b, a ∈ t ∧ t ⊆ s₁ ∩ s₂,
      from hb _ hs₁ _ hs₂ a ⟨has₁, has₂⟩,
    refine ⟨⟨t, hta, htb⟩, _⟩,
    simp only [subset_inter_iff] at ht,
    simp only [principal_mono, subtype.coe_mk, (≥)],
    exact ⟨inter_subset_inter_left _ ht.1, inter_subset_inter_left _ ht.2⟩ },
  rintros ⟨s, hsa, hsb⟩,
  suffices : (s ∩ ⋃ t ∈ b, {f t ‹_›}).nonempty, { simpa [principal_ne_bot_iff] },
  refine ⟨_, hf _ hsb, _⟩,
  simp only [mem_Union],
  exact ⟨s, hsb, rfl⟩
end

variables {α}

lemma is_open_Union_countable [second_countable_topology α]
  {ι} (s : ι → set α) (H : ∀ i, is_open (s i)) :
  ∃ T : set ι, countable T ∧ (⋃ i ∈ T, s i) = ⋃ i, s i :=
let ⟨B, cB, _, bB⟩ := is_open_generated_countable_inter α in
begin
  let B' := {b ∈ B | ∃ i, b ⊆ s i},
  choose f hf using λ b:B', b.2.2,
  haveI : encodable B' := (cB.mono (sep_subset _ _)).to_encodable,
  refine ⟨_, countable_range f,
    subset.antisymm (bUnion_subset_Union _ _) (sUnion_subset _)⟩,
  rintro _ ⟨i, rfl⟩ x xs,
  rcases mem_basis_subset_of_mem_open bB xs (H _) with ⟨b, hb, xb, bs⟩,
  exact ⟨_, ⟨_, rfl⟩, _, ⟨⟨⟨_, hb, _, bs⟩, rfl⟩, rfl⟩, hf _ (by exact xb)⟩
end

lemma is_open_sUnion_countable [second_countable_topology α]
  (S : set (set α)) (H : ∀ s ∈ S, is_open s) :
  ∃ T : set (set α), countable T ∧ T ⊆ S ∧ ⋃₀ T = ⋃₀ S :=
let ⟨T, cT, hT⟩ := is_open_Union_countable (λ s:S, s.1) (λ s, H s.1 s.2) in
⟨subtype.val '' T, cT.image _,
  image_subset_iff.2 $ λ ⟨x, xs⟩ xt, xs,
  by rwa [sUnion_image, sUnion_eq_Union]⟩

end topological_space
