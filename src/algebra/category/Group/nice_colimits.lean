/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Group.basic
import category_theory.limits.limits
import data.dfinsupp
import group_theory.quotient_group

/-!
# The category of additive commutative groups has all colimits.

In `AddCommGroup` there is a much nicer model of colimits as quotients
of finitely supported functions.
-/

universes u v

open category_theory
open category_theory.limits

namespace AddCommGroup.colimits

open dfinsupp
open_locale classical
noncomputable theory

variables {J : Type v} [small_category J] (F : J ⥤ AddCommGroup.{v})

@[derive add_comm_group]
def dfinsupp : Type v := Π₀ j, F.obj j

def relations : set (dfinsupp F) := set.range (λ p : Σ (j j' : J) (f : j ⟶ j'), F.obj j, single p.2.1 (F.map p.2.2.1 p.2.2.2) - single p.1 p.2.2.2)

@[derive add_comm_group]
def colimit_type : Type v := quotient_add_group.quotient (add_group.closure (relations F))

-- TODO why this this not always an instance?
attribute [instance] normal_add_subgroup_of_add_comm_group

def mk_hom : dfinsupp F →+ colimit_type F := add_monoid_hom.of quotient_add_group.mk
def single_hom (j) : F.obj j ⟶ AddCommGroup.of (dfinsupp F) := add_monoid_hom.of (single j)

def colimit_cocone : cocone F :=
{ X := AddCommGroup.of (colimit_type F),
  ι :=
  { app := λ j, single_hom F j ≫ mk_hom F,
    naturality' := λ j j' f, begin ext, dsimp, simp, apply quot.sound, sorry end } }

def desc_fun (s : cocone F) : (colimit_cocone F).X → s.X :=
quot.lift (λ (p : dfinsupp F), @dfinsupp.sum _ _ _ s.X _ _ _ p (λ j x, s.ι.app j x)) sorry

instance (s : cocone F) : is_add_group_hom (desc_fun F s) := sorry

def colimit_is_colimit : is_colimit (colimit_cocone F) :=
{ desc := λ s, add_monoid_hom.of (desc_fun F s),
  fac' := sorry,
  uniq' := sorry, }

instance has_colimits_AddCommGroup : has_colimits.{v} AddCommGroup.{v} :=
{ has_colimits_of_shape := λ J 𝒥,
  { has_colimit := λ F, by exactI
    { cocone := colimit_cocone F,
      is_colimit := colimit_is_colimit F } } }

end AddCommGroup.colimits
