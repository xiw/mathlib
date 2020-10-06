import algebra.module.submodule.lattice

namespace submodule

variables {R M M₂ M₃ : Type*}

section add_comm_group

variables [ring R] [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃]
variables [semimodule R M] [semimodule R M₂] [semimodule R M₃]
variables (p p' : submodule R M) (q q' : submodule R M₂)
variables {r : R} {x y : M}
open set

-- TODO(Mario): Factor through add_subgroup
/-- The equivalence relation associated to a submodule `p`, defined by `x ≈ y` iff `y - x ∈ p`. -/
def quotient_rel : setoid M :=
⟨λ x y, x - y ∈ p, λ x, by simp,
 λ x y h, by simpa using neg_mem _ h,
 λ x y z h₁ h₂, by simpa [sub_eq_add_neg, add_left_comm, add_assoc] using add_mem _ h₁ h₂⟩

/-- The quotient of a module `M` by a submodule `p ⊆ M`. -/
def quotient : Type* := quotient (quotient_rel p)

namespace quotient

/-- Map associating to an element of `M` the corresponding element of `M/p`,
when `p` is a submodule of `M`. -/
def mk {p : submodule R M} : M → quotient p := quotient.mk'

@[simp] theorem mk_eq_mk {p : submodule R M} (x : M) : (quotient.mk x : quotient p) = mk x := rfl
@[simp] theorem mk'_eq_mk {p : submodule R M} (x : M) : (quotient.mk' x : quotient p) = mk x := rfl
@[simp] theorem quot_mk_eq_mk {p : submodule R M} (x : M) : (quot.mk _ x : quotient p) = mk x := rfl

protected theorem eq {x y : M} : (mk x : quotient p) = mk y ↔ x - y ∈ p := quotient.eq'

instance : has_zero (quotient p) := ⟨mk 0⟩
instance : inhabited (quotient p) := ⟨0⟩

@[simp] theorem mk_zero : mk 0 = (0 : quotient p) := rfl

@[simp] theorem mk_eq_zero : (mk x : quotient p) = 0 ↔ x ∈ p :=
by simpa using (quotient.eq p : mk x = 0 ↔ _)

instance : has_add (quotient p) :=
⟨λ a b, quotient.lift_on₂' a b (λ a b, mk (a + b)) $
  λ a₁ a₂ b₁ b₂ h₁ h₂, (quotient.eq p).2 $
    by simpa [sub_eq_add_neg, add_left_comm, add_comm] using add_mem p h₁ h₂⟩

@[simp] theorem mk_add : (mk (x + y) : quotient p) = mk x + mk y := rfl

instance : has_neg (quotient p) :=
⟨λ a, quotient.lift_on' a (λ a, mk (-a)) $
 λ a b h, (quotient.eq p).2 $ by simpa using neg_mem p h⟩

@[simp] theorem mk_neg : (mk (-x) : quotient p) = -mk x := rfl

instance : add_comm_group (quotient p) :=
by refine {zero := 0, add := (+), neg := has_neg.neg, ..};
   repeat {rintro ⟨⟩};
   simp [-mk_zero, (mk_zero p).symm, -mk_add, (mk_add p).symm, -mk_neg, (mk_neg p).symm]; cc

instance : has_scalar R (quotient p) :=
⟨λ a x, quotient.lift_on' x (λ x, mk (a • x)) $
 λ x y h, (quotient.eq p).2 $ by simpa [smul_sub] using smul_mem p a h⟩

@[simp] theorem mk_smul : (mk (r • x) : quotient p) = r • mk x := rfl

instance : semimodule R (quotient p) :=
semimodule.of_core $ by refine {smul := (•), ..};
  repeat {rintro ⟨⟩ <|> intro}; simp [smul_add, add_smul, smul_smul,
    -mk_add, (mk_add p).symm, -mk_smul, (mk_smul p).symm]

lemma mk_surjective : function.surjective (@mk _ _ _ _ _ p) :=
by { rintros ⟨x⟩, exact ⟨x, rfl⟩ }

lemma nontrivial_of_lt_top (h : p < ⊤) : nontrivial (p.quotient) :=
begin
  obtain ⟨x, _, not_mem_s⟩ := exists_of_lt h,
  refine ⟨⟨mk x, 0, _⟩⟩,
  simpa using not_mem_s
end

end quotient

lemma quot_hom_ext ⦃f g : quotient p →ₗ[R] M₂⦄ (h : ∀ x, f (quotient.mk x) = g (quotient.mk x)) :
  f = g :=
linear_map.ext $ λ x, quotient.induction_on' x h

end add_comm_group

end submodule
