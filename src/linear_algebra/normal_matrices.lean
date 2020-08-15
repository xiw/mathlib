import data.complex.basic
import data.fintype.basic
import data.matrix.basic
import linear_algebra.unitary_group
import linear_algebra.determinant
import linear_algebra.nonsingular_inverse
import tactic

noncomputable theory
open_locale classical
open_locale matrix

universes u u'
variables {m n l : Type u} [fintype m] [fintype n] [fintype l]

local notation `Euc` := (n → ℂ)


section upper_triangular
def matrix.upper_triangular [linear_order n] (A : matrix n n ℂ) :=
  ∀ i j, (i < j) → (A i j = 0)

end upper_triangular

section normal
def matrix.normal (A : matrix n n ℂ) :=
  A * A.conjugate_transpose = A.conjugate_transpose * A

theorem diagonal_of_upper_triangular_normal [linear_order n] {A : matrix n n ℂ}
  (hAu : A.upper_triangular) (hAn : A.normal) : ∃ D : n → ℂ, A = matrix.diagonal D
:= sorry

end normal



-- todo later:

-- @[ext]
-- structure unitary_matrices (n : Type u) [fintype n]:=
-- (val : matrix n n ℂ)
-- (is_unitary : val.unitary)


-- instance : group (unitary_matrices n) :=
-- { mul := λ A B,
--   { val := A.val ⬝ B.val,
--   is_unitary := unitary.has_mul A.is_unitary B.is_unitary},
--   mul_assoc := λ A B C, sorry ,
--   one := { val := (1 : matrix n n ℂ),
--     is_unitary := unitary.has_one},
--   one_mul := λ A, by { },
--   mul_one := sorry,
--   inv := sorry,
--   mul_left_inv := sorry}



-- section symmetric

-- end symmetric

-- section skew_symmtric

-- end skew_symmtric


-- section hermitian
-- def hermitian (A : matrix n n ℂ) :=
--   A = A.conjugate_transpose
-- end hermitian


-- section anti_hermitian

-- end anti_hermitian
-- -- structure units (ℂ : Type u) [monoid ℂ] :=
-- -- (val : ℂ)
-- -- (inv : ℂ)
-- -- (val_inv : val * inv = 1)
-- -- (inv_val : inv * val = 1)

-- theorem normal_of_hermitian {A : matrix n n ℂ} (hh : hermitian A) : normal A :=
--   by {unfold normal, unfold hermitian at hh, rw ←hh,}

-- theorem normal_of_unitary {A : matrix n n ℂ} (hu : A.unitary) : normal A :=
-- sorry
-- end normal
