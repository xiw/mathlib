import data.fintype.card

variables (α : Type*) [fintype α] [decidable_eq α]

open_locale big_operators nat
open equiv (perm) fintype

namespace imo_1987_q1

@[derive fintype]
def fiber (k : ℕ) : set (perm α) := {σ : perm α | card {x | σ x = x} = k}

def p (k : ℕ) := card (fiber α k)

local notation `n` := card α

theorem card_fixed_points : card {σx : α × perm α | σx.2 σx.1 = σx.1} = (card α)! :=
calc card {σx : α × perm α | σx.2 σx.1 = σx.1} = card (Σ x : α, {σ : perm α | σ x = x}) :
  card_congr (equiv.set_prod_equiv_sigma _)
... = ∑ x, card {σ : perm α | σ x = x} : card_sigma _
... = ∑ x, 

-- theorem main : ∑ k in finset.range (card α + 1), k * p α k = (card α)! :=
-- have ∀ k (σ : fiber α k), card {x | σ.1 x = x} = k := λ k σ, σ.2,
-- calc ∑ k in range (n + 1), k * p α k =
--   ∑ k in range (n + 1), card (Σ σ : fiber α k, {x | σ.1 x = x}) :
--   by simp_rw [fintype.card_sigma, this, sum_const, p, nat.nsmul_eq_mul, mul_comm, fintype.card]
-- ... = _ : _

end imo_1987_q1
