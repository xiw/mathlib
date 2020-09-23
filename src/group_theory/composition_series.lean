import group_theory.quotient_group
import data.fintype.basic

/- We'll try to make a small demo for composition series using mathlib's version
  of groups. -/

open_locale classical

namespace composition_series

variables {G : Type*} [group G]

def subgroup.le_hom {A B : subgroup G} (hAB : A ≤ B) : A →* B :=
  monoid_hom.mk' (λ a, ⟨a.1, hAB a.2⟩) (λ _ _, rfl)

def subgroup.normal_pair {A B : subgroup G} (hAB : A ≤ B) : Prop :=
  (monoid_hom.range (subgroup.le_hom hAB)).normal

@[simp] lemma subgroup.normal_pair_def {A B : subgroup G} (hAB : A ≤ B) :
  subgroup.normal_pair hAB ↔ (monoid_hom.range (subgroup.le_hom hAB)).normal := iff.rfl

def subgroup.normal_pair' (A B : subgroup G): Prop :=
  (monoid_hom.range (subgroup.le_hom (show A ⊓ B ≤ B, by exact inf_le_right))).normal

open quotient_group set

variables (H N : subgroup G) [nN : N.normal]

local notation G ` /ₘ ` N := @quotient_group.quotient G _ N

def is_simple (G : Type*) [group G] :=
  ∀ (N : subgroup G), N.normal → N = ⊥ ∨ N = ⊤

def normal_chain_prop (A B : subgroup G) : Prop :=
  ∃ (hle : A ≤ B) (hn : subgroup.normal_pair hle),
  @is_simple (B /ₘ monoid_hom.range (subgroup.le_hom hle))
  (by { rw subgroup.normal_pair_def at hn, resetI, apply_instance })

@[simp] lemma normal_chain_prop_def {A B : subgroup G} :
  normal_chain_prop A B ↔
  ∃ (hle : A ≤ B) (hn : subgroup.normal_pair hle),
  @is_simple (B /ₘ monoid_hom.range (subgroup.le_hom hle))
  (by { rw subgroup.normal_pair_def at hn, resetI, apply_instance }) := iff.rfl

structure normal_chain (G : Type*) [group G] :=
(carrier    : list (subgroup G))
(chain_prop : carrier.chain' normal_chain_prop)

example [fintype G] :
  ∃ (N : subgroup G) (hN : N.normal), @is_simple (G /ₘ N) (by resetI; apply_instance) :=
begin
  -- The idea is to use the largest normal subgroup of G thats ≠ G
  sorry
end

end composition_series
