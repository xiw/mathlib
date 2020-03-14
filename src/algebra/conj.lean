/-
Copyright (c) 2018  Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Chris Hughes, Michael Howes, Yury Kudryashov
-/
import tactic.basic data.equiv.mul_add
/-!
# Conjugacy of group elements
-/

universes u v
variables (G : Type u) {H : Type v}

variables [group G] [group H]

/-- `conj g h = g * h * g⁻¹`, defined as a monoid homomorphism from `G` to `mul_aut G`. -/
def conj : G →* mul_aut G :=
{ to_fun := λ g,
  { to_fun := λ h, g * h * g⁻¹,
    inv_fun := λ h, g⁻¹ * h * g,
    left_inv := λ h, by simp only [mul_assoc, inv_mul_cancel_left, mul_left_inv, mul_one],
    right_inv := λ h, by simp only [mul_assoc, mul_right_inv, mul_one, mul_inv_cancel_left],
    map_mul' := λ h₁ h₂, by simp only [mul_assoc, inv_mul_cancel_left] },
  map_mul' := λ g₁ g₂, by { ext h, simp [mul_assoc] },
  map_one' := by { ext h, simp } }

lemma conj_apply (g h : G) : conj G g h = g * h * g⁻¹ := rfl

variable {G}

/-- `is_conj a b` means that some element `c`` conjugates `a` to `b`. -/
def is_conj (a b : G) := ∃ c : G, conj G c a = b

@[refl] lemma is_conj_refl (a : G) : is_conj a a :=
⟨1, by rw [(conj G).map_one, mul_aut.one_apply]⟩

@[symm] lemma is_conj.symm {a b : G} : is_conj a b → is_conj b a
| ⟨c, hc⟩ := ⟨c⁻¹, by rw [← hc, ← mul_aut.mul_apply, ← monoid_hom.map_mul, mul_left_inv,
  monoid_hom.map_one, mul_aut.one_apply]⟩

lemma is_conj_symm {a b : G} : is_conj a b ↔ is_conj b a :=
⟨λ h, h.symm, λ h, h.symm⟩

@[trans] lemma is_conj.trans {a b c : G} : is_conj a b → is_conj b c → is_conj a c
| ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩ := ⟨c₂ * c₁, by rw [← hc₂, ← hc₁, (conj G).map_mul, mul_aut.mul_apply]⟩

@[simp] lemma is_conj_one_right {a : G} : is_conj 1 a ↔ a = 1 :=
⟨by simp [is_conj, is_conj_refl] {contextual := tt}, by simp [is_conj_refl] {contextual := tt}⟩

@[simp] lemma is_conj_one_left {a : G} : is_conj a 1 ↔ a = 1 :=
calc is_conj a 1 ↔ is_conj 1 a : is_conj_symm
... ↔ a = 1 : is_conj_one_right

@[simp] lemma conj_eq_self {G : Type*} [comm_group G] (a b : G) : conj G a b = b :=
by rw [conj_apply, mul_right_comm, mul_inv_self, one_mul]

@[simp] lemma is_conj_iff_eq {G : Type*} [comm_group G] {a b : G} : is_conj a b ↔ a = b :=
⟨λ ⟨c, hc⟩, by rw [← hc, conj_eq_self], λ h, by rw h⟩

protected lemma monoid_hom.map_conj (f : G →* H) {a b : G} :
  f (conj G a b) = conj H (f a) (f b) :=
by rw [conj_apply, conj_apply, f.map_mul, f.map_mul, f.map_inv]

protected lemma monoid_hom.map_is_conj (f : G →* H) {a b : G} : is_conj a b → is_conj (f a) (f b)
| ⟨c, hc⟩ := ⟨f c, by rw [← hc, f.map_conj]⟩
