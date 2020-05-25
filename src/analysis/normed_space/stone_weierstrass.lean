import analysis.normed_space.basic
import group_theory.bundled_subgroup

variables (X : Type*) [topological_space X]
variables (Y : Type*) [topological_space Y]

/-- Continuous functions. -/
def C (X Y : Type*) [topological_space X] [topological_space Y] : set (X → Y) :=
{ f : X → Y | continuous f }

section
variables [add_monoid Y] [topological_add_monoid Y]

def C_add_submonoid : add_submonoid (X → Y) :=
{ carrier := C X Y,
  zero_mem' := begin simp [C], convert continuous_const, swap, exact 0, refl, end,  -- YUCK
  add_mem' := λ f g fc gc, continuous.add fc gc, }

instance : add_monoid (C X Y) := (C_add_submonoid X Y).to_add_monoid
end

section
variables [add_group Y] [topological_add_group Y]

def C_add_subgroup : add_subgroup (X → Y) :=
{ neg_mem' := λ f fc, continuous.neg fc,
  ..(C_add_submonoid X Y) }

instance : add_group (C X Y) := (C_add_subgroup X Y).to_add_group
end

open filter
open_locale topological_space

/-- The filter on X consisting of sets U such that the closure of the complement of U is compact. -/
def ccc : filter X :=
{ sets := { U : set X | compact (closure (-U)) },
  univ_sets := by simp,
  sets_of_superset := λ U V mU ss,
  begin
    simp at *,
    apply compact_of_is_closed_subset mU,
    { simp, },
    { rw set.compl_subset_compl, -- TODO should be a simp lemma?
      exact interior_mono ss, },
  end,
  inter_sets := λ U V mU mV,
  begin
    simp at *,
    rw set.compl_inter,
    exact compact.union mU mV,
  end }

/-- Continuous functions vanishing at infinity. -/
def C₀ (X Y : Type*) [topological_space X] [topological_space Y] [has_zero Y] : set (C X Y) :=
{ f : C X Y | tendsto f.1 (ccc X) (𝓝 0) }


section
variables [add_monoid Y] [topological_add_monoid Y]

def C₀_add_submonoid : add_submonoid (C X Y) :=
{ carrier := C₀ X Y,
  zero_mem' := begin simp [C₀], apply @tendsto_const_nhds _ _ _ (0 : Y) (ccc X), end,
  add_mem' := λ f g ft gt, begin simp [C₀] at *, convert tendsto.add ft gt, simp, end, }

instance : add_monoid (C₀ X Y) := (C₀_add_submonoid X Y).to_add_monoid
end
