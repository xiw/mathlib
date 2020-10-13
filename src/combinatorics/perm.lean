import data.equiv.basic

open set
namespace equiv
namespace perm

variables {α : Type*}

def perm_restict_eq_equiv_perm_compl {s : set α} [decidable_pred s] (σs : perm s) :
  {σ : perm α // ∀ x : s, σ x = σs x} ≃ perm (sᶜ : set α) :=
begin
  refine { to_fun := λ σ, σ.1.subtype_congr _, inv_fun := λ σ, ⟨_, _⟩, .. },
  { refine λ a, not_congr _,
    rcases σ with ⟨σ, hσ⟩,
    have hσ' : ∀ a ∈ s, σ a = σs ⟨a, ‹_›⟩ := subtype.forall.1 hσ,
    split; intro ha,
    { simp [hσ' _ ha] },
    { have := hσ (σs.symm ⟨_, ha⟩),
      simp at this, } }
end

end perm
end equiv
