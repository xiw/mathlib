/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import category_theory.concrete_category
import order.basic

/-!
# Category instances for ordered structures

We introduce
* Preorder     : the category of preorders and monotone functions.
* PartialOrder : the category of partial orders and monotone functions.
* LinOrder     : the category of linear orders and monotone functions.
* DecLinOrder  : the category of decidable linear orders and monotone functions.

and the appropriate forgetful functors between them.

## Implementation notes

See the note [locally reducible category instances].
-/


universes u v

open category_theory

/-- The category of preorders and monotone maps. -/
def Preorder : Type (u+1) := bundled preorder

namespace Preorder
local attribute [reducible] Preorder

def of (X : Type u) [preorder X] : Preorder := bundled.of X

instance : unbundled_hom @monotone :=
⟨@monotone_id, (λ _ _ _ _ _ _ _ _ m₁ m₂, by exactI monotone.comp m₁ m₂)⟩

instance (X : Preorder) : preorder X := X.str

instance : has_coe_to_sort Preorder := infer_instance

instance : concrete_category Preorder.{u} := infer_instance
end Preorder

/-- The category of partial orders and monotone maps. -/
def PartialOrder : Type (u+1) := induced_category Preorder (bundled.map partial_order.to_preorder.{u})

namespace PartialOrder
local attribute [reducible] PartialOrder

instance (X : PartialOrder) : partial_order X := X.str

instance : has_coe_to_sort PartialOrder := infer_instance

def of (X : Type u) [partial_order X] : PartialOrder := bundled.of X

instance : concrete_category PartialOrder.{u} := infer_instance
instance : has_forget₂ PartialOrder.{u} Preorder.{u} := infer_instance

end PartialOrder

/-- The category of linear orders and monotone maps. -/
def LinOrder : Type (u+1) := induced_category PartialOrder (bundled.map linear_order.to_partial_order.{u})

namespace LinOrder
local attribute [reducible] LinOrder

instance (X : LinOrder) : linear_order X := X.str

instance : has_coe_to_sort LinOrder := infer_instance

def of (X : Type u) [linear_order X] : LinOrder := bundled.of X

instance : concrete_category LinOrder.{u} := infer_instance
instance : has_forget₂ LinOrder.{u} PartialOrder.{u} := infer_instance

end LinOrder

/-- The category of decidable linear orders and monotone maps. -/
def DecLinOrder : Type (u+1) := induced_category LinOrder (bundled.map decidable_linear_order.to_linear_order.{u})

namespace DecLinOrder
local attribute [reducible] DecLinOrder

instance (X : DecLinOrder) : decidable_linear_order X := X.str

instance : has_coe_to_sort DecLinOrder := infer_instance

def of (X : Type u) [decidable_linear_order X] : DecLinOrder := bundled.of X

instance : concrete_category DecLinOrder.{u} := infer_instance
instance : has_forget₂ DecLinOrder.{u} LinOrder.{u} := infer_instance

end DecLinOrder
