/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import algebra.group.basic

/-!
# Racks and Quandles

This file defines racks and quandles, algebraic structures that encode group conjugation
  and knot invariants.

## Main definitions

• `rack`
• `quandle`
• `rack.of_ql` defines a rack from just its left operation
• `rack.of_qr` defines a rack from just its right operation
• `quandle.of_group` defines a quandle which encodes the conjugation operation of a group

## Main statements
• Not much yet

## Tags

rack, quandle
-/

variable {α : Type*}

set_option default_priority 100 -- see Note [default priority]
set_option old_structure_cmd true

class rack (α : Type*) :=
(ql : α → α → α)
(qr : α → α → α)
(self_distrib_left : ∀ a b c, ql a (ql b c) = ql (ql a b) (ql a c))
(self_distrib_right : ∀ a b c, qr (qr c b) a = qr (qr c a) (qr b a))
(qr_ql : ∀ a b, qr (ql a b) a = b)
(ql_qr : ∀ a b, ql a (qr b a) = b)

variable {α}

local infix ` ◃ ` : 50 := rack.ql
local infix ` ▹ ` : 50 := rack.qr

namespace rack
section rack_of

variables {q : α → α → α}

noncomputable theory

/-- Given a right-quandle operation, constructs the matching left-quandle operation -/
def qr_of_ql (hl : ∀ a b, ∃! c, q a c = b) (a b : α) : α := classical.some (hl b a)

lemma qr_of_ql_apply (hl : ∀ a b, ∃! c, q a c = b) {a b c : α} :
  (rack.qr_of_ql hl) b a = c ↔ q a c = b :=
⟨λ h, h ▸ (classical.some_spec (hl a b)).1,
  λ h, (hl a b).unique (h ▸ (classical.some_spec (hl a (q a c))).1) h⟩

lemma ql_qr_of_qr_of_ql {hl : ∀ a b, ∃! c, q a c = b} {a b : α} :
  q a (qr_of_ql hl b a) = b := (qr_of_ql_apply hl).1 rfl
lemma qr_ql_of_qr_of_ql {hl : ∀ a b, ∃! c, q a c = b} {a b : α} :
  qr_of_ql hl (q a b) a = b := (qr_of_ql_apply hl).2 rfl

/-- Given a left-quandle operation, constructs the quandle -/
def of_ql (self_distrib : ∀ a b c, q a (q b c) = q (q a b) (q a c)) (hl : ∀ a b, ∃! c, q a c = b) :
  rack α :=
{ ql := q,
  self_distrib_left := λ a b c, self_distrib a b c,
  qr := rack.qr_of_ql hl,
  ql_qr := λ a b, ql_qr_of_qr_of_ql,
  qr_ql := λ a b, qr_ql_of_qr_of_ql,
  self_distrib_right := λ a b c, by {
    symmetry, rw qr_of_ql_apply, symmetry, rw qr_of_ql_apply, rw self_distrib,
    transitivity q b (q a (qr_of_ql hl (qr_of_ql hl c b) a)),
    {refine congr (congr rfl _) rfl, apply ql_qr_of_qr_of_ql},
    rw ← qr_of_ql_apply hl, symmetry, rw ← qr_of_ql_apply hl,
  },
}

/-- Given a left-quandle operation, constructs the matching right-quandle operation -/
def ql_of_qr (hr : ∀ a b, ∃! c, q c a = b) (a b : α) : α := classical.some (hr a b)

lemma ql_of_qr_apply (hr : ∀ a b, ∃! c, q c a = b) {a b c : α} :
  (rack.ql_of_qr hr) a c = b ↔ q b a = c :=
⟨λ h, h ▸ (classical.some_spec (hr a c)).1,
  λ h, (hr a c).unique (h ▸ (classical.some_spec (hr a (q b a))).1) h⟩

lemma ql_qr_of_ql_of_qr {hr : ∀ a b, ∃! c, q c a = b} {a b : α} :
  ql_of_qr hr a (q b a) = b := (qr_of_ql_apply hr).2 rfl
lemma qr_ql_of_ql_of_qr {hr : ∀ a b, ∃! c, q c a = b} {a b : α} :
  q (ql_of_qr hr a b) a = b := (qr_of_ql_apply hr).1 rfl

/-- Given a right-quandle operation, constructs the quandle -/
def of_qr (self_distrib : ∀ a b c, q (q c b) a = q (q c a) (q b a)) (hr : ∀ a b, ∃! c, q c a = b) :
  rack α :=
{ qr := q,
  self_distrib_right := λ a b c, self_distrib a b c,
  ql := rack.ql_of_qr hr,
  ql_qr := λ a b, ql_qr_of_ql_of_qr,
  qr_ql := λ a b, qr_ql_of_ql_of_qr,
  self_distrib_left := λ a b c, by {
    symmetry, rw ql_of_qr_apply, symmetry, rw ql_of_qr_apply, rw self_distrib,
    transitivity q (q (ql_of_qr hr a (ql_of_qr hr b c)) a) b,
    {refine congr rfl _, apply qr_ql_of_ql_of_qr},
    rw ← ql_of_qr_apply hr, symmetry, rw ← ql_of_qr_apply hr,
  },
}

end rack_of

variable [rack α]

attribute [simp] qr_ql ql_qr

end rack

@[protect_proj, ancestor rack]
class quandle (α : Type*) extends rack α :=
(ql_idem : ∀ a, ql a a = a)

attribute [simp] quandle.ql_idem

namespace quandle

section of_group

variable [group α]

/-- A quandle encoding the conjugation information of a group -/
def of_group [group α] : quandle α :=
{ ql := λ a b, a * b * a⁻¹,
  qr := λ a b, b⁻¹ * a * b,
  qr_ql := λ a b, by simp [← mul_assoc],
  ql_qr := λ a b, by simp [← mul_assoc],
  self_distrib_left := λ a b, by simp [← mul_assoc],
  self_distrib_right := λ a b, by simp [← mul_assoc],
  ql_idem := λ a, by simp, }

end of_group

variable [quandle α]

lemma qr_idem (a : α) : a ▹ a = a := sorry

end quandle
