/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import data.mv_polynomial
import ring_theory.ideal.over
import ring_theory.jacobson_ideal
import ring_theory.localization

/-!
# Jacobson Rings

The following conditions are equivalent for a ring `R`:
1. Every radical ideal `I` is equal to its jacobson radical
2. Every radical ideal `I` can be written as an intersection of maximal ideals
3. Every prime ideal `I` is equal to its jacobson radical

Any ring satisfying any of these equivalent conditions is said to be Jacobson.

Some particular examples of Jacobson rings are also proven.
`is_jacobson_quotient` says that the quotient of a Jacobson ring is Jacobson.
`is_jacobson_localization` says the localization of a Jacobson ring to a single element is Jacobson.

## Main definitions

Let `R` be a commutative ring. Jacobson Rings are defined using the first of the above conditions

* `is_jacobson R` is the proposition that `R` is a Jacobson ring. It is a class,
  implemented as the predicate that for any ideal, `I.radical = I` implies `I.jacobson = I`.

## Main statements

* `is_jacobson_iff_prime_eq` is the equivalence between conditions 1 and 3 above.

* `is_jacobson_iff_Inf_maximal` is the equivalence between conditions 1 and 2 above.

* `is_jacobson_of_surjective` says that if `R` is a Jacobson ring and `f : R →+* S` is surjective,
  then `S` is also a Jacobson ring

## Tags

Jacobson, Jacobson Ring

-/

universes u v

namespace ideal
variables {R : Type u} [comm_ring R] {I : ideal R}
variables {S : Type v} [comm_ring S]

section is_jacobson

/-- A ring is a Jacobson ring if for every radical ideal `I`,
 the Jacobson radical of `I` is equal to `I`.
 See `is_jacobson_iff_prime_eq` and `is_jacobson_iff_Inf_maximal` for equivalent definitions. -/
@[class] def is_jacobson (R : Type u) [comm_ring R] :=
    ∀ (I : ideal R), I.radical = I → I.jacobson = I

/--  A ring is a Jacobson ring if and only if for all prime ideals `P`,
 the Jacobson radical of `P` is equal to `P`. -/
lemma is_jacobson_iff_prime_eq : is_jacobson R ↔ ∀ P : ideal R, is_prime P → P.jacobson = P :=
begin
  split,
  { exact λ h I hI, h I (is_prime.radical hI) },
  { refine λ h I hI, le_antisymm (λ x hx, _) (λ x hx, mem_Inf.mpr (λ _ hJ, hJ.left hx)),
    erw mem_Inf at hx,
    rw [← hI, radical_eq_Inf I, mem_Inf],
    intros P hP,
    rw set.mem_set_of_eq at hP,
    erw [← h P hP.right, mem_Inf],
    exact λ J hJ, hx ⟨le_trans hP.left hJ.left, hJ.right⟩ }
end

/-- A ring `R` is Jacobson if and only if for every prime ideal `I`,
 `I` can be written as the infimum of some collection of maximal ideals.
 Allowing ⊤ in the set `M` of maximal ideals is equivalent, but makes some proofs cleaner. -/
lemma is_jacobson_iff_Inf_maximal : is_jacobson R ↔
  ∀ {I : ideal R}, I.is_prime → ∃ M : set (ideal R), (∀ J ∈ M, is_maximal J ∨ J = ⊤) ∧ I = Inf M :=
⟨λ H I h, eq_jacobson_iff_Inf_maximal.1 (H _ (is_prime.radical h)),
  λ H , is_jacobson_iff_prime_eq.2 (λ P hP, eq_jacobson_iff_Inf_maximal.2 (H hP))⟩

lemma is_jacobson_iff_Inf_maximal' : is_jacobson R ↔
  ∀ {I : ideal R}, I.is_prime → ∃ M : set (ideal R), (∀ (J ∈ M) (K : ideal R), J < K → K = ⊤) ∧ I = Inf M :=
⟨λ H I h, eq_jacobson_iff_Inf_maximal'.1 (H _ (is_prime.radical h)),
  λ H , is_jacobson_iff_prime_eq.2 (λ P hP, eq_jacobson_iff_Inf_maximal'.2 (H hP))⟩

lemma radical_eq_jacobson (H : is_jacobson R) (I : ideal R) : I.radical = I.jacobson :=
le_antisymm (le_Inf (λ J ⟨hJ, hJ_max⟩, (is_prime.radical_le_iff hJ_max.is_prime).mpr hJ))
            ((H I.radical (radical_idem I)) ▸ (jacobson_mono le_radical))

/-- Fields have only two ideals, and the condition holds for both of them -/
@[priority 100]
instance is_jacobson_field {K : Type u} [field K] : is_jacobson K :=
λ I hI, or.rec_on (eq_bot_or_top I)
(λ h, le_antisymm
  (Inf_le ⟨le_of_eq rfl, (eq.symm h) ▸ bot_is_maximal⟩)
  ((eq.symm h) ▸ bot_le))
(λ h, by rw [h, jacobson_eq_top_iff])

theorem is_jacobson_of_surjective [H : is_jacobson R] :
  (∃ (f : R →+* S), function.surjective f) → is_jacobson S :=
begin
  rintros ⟨f, hf⟩,
  rw is_jacobson_iff_Inf_maximal,
  intros p hp,
  use map f '' {J : ideal R | comap f p ≤ J ∧ J.is_maximal },
  use λ j ⟨J, hJ, hmap⟩, hmap ▸ or.symm (map_eq_top_or_is_maximal_of_surjective f hf hJ.right),
  have : p = map f ((comap f p).jacobson),
  from (H (comap f p) (by rw [← comap_radical, is_prime.radical hp])).symm
    ▸ (map_comap_of_surjective f hf p).symm,
  exact eq.trans this (map_Inf hf (λ J ⟨hJ, _⟩, le_trans (ideal.ker_le_comap f) hJ)),
end

@[priority 100]
instance is_jacobson_quotient [is_jacobson R] : is_jacobson (quotient I) :=
is_jacobson_of_surjective ⟨quotient.mk I, (by rintro ⟨x⟩; use x; refl)⟩

lemma is_jacobson_iso (e : R ≃+* S) : is_jacobson R ↔ is_jacobson S :=
⟨λ h, @is_jacobson_of_surjective _ _ _ _ h ⟨(e : R →+* S), e.surjective⟩,
  λ h, @is_jacobson_of_surjective _ _ _ _ h ⟨(e.symm : S →+* R), e.symm.surjective⟩⟩

lemma is_jacobson_of_is_integral [algebra R S] (hRS : algebra.is_integral R S)
  (hR : is_jacobson R) : is_jacobson S :=
begin
  rw is_jacobson_iff_prime_eq,
  introsI P hP,
  by_cases hP_top : comap (algebra_map R S) P = ⊤,
  { simp [comap_eq_top_iff.1 hP_top] },
  { haveI : nontrivial (comap (algebra_map R S) P).quotient := quotient.nontrivial hP_top,
    rw jacobson_eq_iff_jacobson_quotient_eq_bot,
    refine eq_bot_of_comap_eq_bot (is_integral_quotient_of_is_integral hRS) _,
    rw [eq_bot_iff, ← jacobson_eq_iff_jacobson_quotient_eq_bot.1 ((is_jacobson_iff_prime_eq.1 hR)
      (comap (algebra_map R S) P) (comap_is_prime _ _)), comap_jacobson],
    refine Inf_le_Inf (λ J hJ, _),
    simp only [true_and, set.mem_image, bot_le, set.mem_set_of_eq],
    haveI : J.is_maximal := by simpa using hJ,
    exact exists_ideal_over_maximal_of_is_integral (is_integral_quotient_of_is_integral hRS) J
      (comap_bot_le_of_injective _ algebra_map_quotient_injective) }
end

-- lemma is_jacobson_of_is_integral' {f : R →+* S} (hf : f.is_integral)
--   (hR : is_jacobson R) : is_jacobson S :=
-- begin
-- refine @is_jacobson_of_is_integral R _ S _ f.to_algebra _ hR,
-- refine λ x, _,
-- convert hf x,
-- rw to_algebra_algebra
-- end

end is_jacobson


section localization
open localization_map
variables {y : R} (f : away_map y S)

lemma disjoint_powers_iff_not_mem {I : ideal R} (hI : I.radical = I) :
  disjoint ((submonoid.powers y) : set R) ↑I ↔ y ∉ I.1 :=
begin
  refine ⟨λ h, set.disjoint_left.1 h (submonoid.mem_powers _), λ h, _⟩,
  rw [disjoint_iff, eq_bot_iff],
  rintros x ⟨hx, hx'⟩,
  obtain ⟨n, hn⟩ := hx,
  rw [← hn, ← hI] at hx',
  exact absurd (hI ▸ mem_radical_of_pow_mem hx' : y ∈ I.carrier) h
end

/-- If `R` is a Jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y`.
This lemma gives the correspondence in the particular case of an ideal and its comap.
See `le_rel_iso_of_maximal` for the more general relation isomorphism -/
lemma is_maximal_iff_is_maximal_disjoint [H : is_jacobson R] (J : ideal S) :
  J.is_maximal ↔ (comap f.to_map J).is_maximal ∧ y ∉ ideal.comap f.to_map J :=
begin
  split,
  { refine λ h, ⟨_, λ hy, h.1 (ideal.eq_top_of_is_unit_mem _ hy
      (map_units f ⟨y, submonoid.mem_powers _⟩))⟩,
    have hJ : J.is_prime := is_maximal.is_prime h,
    rw is_prime_iff_is_prime_disjoint f at hJ,
    have : y ∉ (comap f.to_map J).1 :=
      set.disjoint_left.1 hJ.right (submonoid.mem_powers _),
    erw [← H (comap f.to_map J) (is_prime.radical hJ.left), mem_Inf] at this,
    push_neg at this,
    rcases this with ⟨I, hI, hI'⟩,
    convert hI.right,
    by_cases hJ : J = map f.to_map I,
    { rw [hJ, comap_map_of_is_prime_disjoint f I (is_maximal.is_prime hI.right)],
      rwa disjoint_powers_iff_not_mem (is_maximal.is_prime hI.right).radical},
    { have hI_p : (map f.to_map I).is_prime,
      { refine is_prime_of_is_prime_disjoint f I hI.right.is_prime _,
        rwa disjoint_powers_iff_not_mem (is_maximal.is_prime hI.right).radical },
      have : J ≤ map f.to_map I := (map_comap f J) ▸ (map_mono hI.left),
      exact absurd (h.right _ (lt_of_le_of_ne this hJ)) hI_p.left } },
  { refine λ h, ⟨λ hJ, h.left.left (eq_top_iff.2 _), λ I hI, _⟩,
    { rwa [eq_top_iff, (order_embedding f).map_rel_iff] at hJ },
    { have := congr_arg (map f.to_map) (h.left.right _ ⟨comap_mono (le_of_lt hI), _⟩),
      rwa [map_comap f I, map_top f.to_map] at this,
      refine λ hI', hI.right _,
      rw [← map_comap f I, ← map_comap f J],
      exact map_mono hI' } }
end

/-- If `R` is a Jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y`.
This lemma gives the correspondence in the particular case of an ideal and its map.
See `le_rel_iso_of_maximal` for the more general statement, and the reverse of this implication -/
lemma is_maximal_of_is_maximal_disjoint [is_jacobson R] (I : ideal R) (hI : I.is_maximal)
  (hy : y ∉ I) : (map f.to_map I).is_maximal :=
begin
  rw [is_maximal_iff_is_maximal_disjoint f,
    comap_map_of_is_prime_disjoint f I (is_maximal.is_prime hI)
    ((disjoint_powers_iff_not_mem (is_maximal.is_prime hI).radical).2 hy)],
  exact ⟨hI, hy⟩
end

/-- If `R` is a Jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y` -/
def order_iso_of_maximal [is_jacobson R] :
  {p : ideal S // p.is_maximal} ≃o {p : ideal R // p.is_maximal ∧ y ∉ p} :=
{ to_fun := λ p, ⟨ideal.comap f.to_map p.1, (is_maximal_iff_is_maximal_disjoint f p.1).1 p.2⟩,
  inv_fun := λ p, ⟨ideal.map f.to_map p.1, is_maximal_of_is_maximal_disjoint f p.1 p.2.1 p.2.2⟩,
  left_inv := λ J, subtype.eq (map_comap f J),
  right_inv := λ I, subtype.eq (comap_map_of_is_prime_disjoint f I.1 (is_maximal.is_prime I.2.1)
    ((disjoint_powers_iff_not_mem I.2.1.is_prime.radical).2 I.2.2)),
  map_rel_iff' := λ I I', ⟨λ h x hx, h hx, λ h, (show I.val ≤ I'.val,
    from (map_comap f I.val) ▸ (map_comap f I'.val) ▸ (ideal.map_mono h))⟩ }

/-- If `S` is the localization of the Jacobson ring `R` at the submonoid generated by `y : R`, then `S` is Jacobson. -/
lemma is_jacobson_localization [H : is_jacobson R]
  (f : away_map y S) : is_jacobson S :=
begin
  rw is_jacobson_iff_prime_eq,
  refine λ P' hP', le_antisymm _ le_jacobson,
  obtain ⟨hP', hPM⟩ := (localization_map.is_prime_iff_is_prime_disjoint f P').mp hP',
  have hP := H (comap f.to_map P') (is_prime.radical hP'),
  refine le_trans (le_trans (le_of_eq (localization_map.map_comap f P'.jacobson).symm) (map_mono _))
    (le_of_eq (localization_map.map_comap f P')),
  have : Inf { I : ideal R | comap f.to_map P' ≤ I ∧ I.is_maximal ∧ y ∉ I } ≤ comap f.to_map P',
  { intros x hx,
    have hxy : x * y ∈ (comap f.to_map P').jacobson,
    { rw [ideal.jacobson, mem_Inf],
      intros J hJ,
      by_cases y ∈ J,
      { exact J.smul_mem x h },
      { exact (mul_comm y x) ▸ J.smul_mem y ((mem_Inf.1 hx) ⟨hJ.left, ⟨hJ.right, h⟩⟩) } },
    rw hP at hxy,
    cases hP'.right hxy with hxy hxy,
    { exact hxy },
    { exfalso,
      refine hPM ⟨submonoid.mem_powers _, hxy⟩ } },
  refine le_trans _ this,
  rw [ideal.jacobson, comap_Inf', Inf_eq_infi],
  refine infi_le_infi_of_subset (λ I hI, ⟨map f.to_map I, ⟨_, _⟩⟩),
  { exact ⟨le_trans (le_of_eq ((localization_map.map_comap f P').symm)) (map_mono hI.1),
    is_maximal_of_is_maximal_disjoint f _ hI.2.1 hI.2.2⟩ },
  { exact localization_map.comap_map_of_is_prime_disjoint f I (is_maximal.is_prime hI.2.1)
    ((disjoint_powers_iff_not_mem hI.2.1.is_prime.radical).2 hI.2.2) }
end

end localization

section polynomial
open polynomial

lemma bot_jacobson_polynomial (h : jacobson (⊥ : ideal R) = ⊥) :
  jacobson (⊥ : ideal (polynomial R)) = ⊥ :=
begin
  have : (Inf (map C '' {J : ideal R | ⊥ ≤ J ∧ J.is_maximal}) : ideal (polynomial R)) = ⊥,
  { rw eq_bot_iff,
    intros f hf,
    rw submodule.mem_bot,
    ext,
    rw coeff_zero,
    suffices : f.coeff n ∈ ⊥, by rwa submodule.mem_bot at this,
    rw [← h, ideal.jacobson],
    rw mem_Inf at *,
    intros j hj,
    have : f ∈ (map C j : ideal (polynomial R)),
    { refine hf _,
      rw set.mem_image,
      refine ⟨j, ⟨hj, rfl⟩⟩ },
    rw mem_map_C_iff at this,
    exact this n },
  rw eq_bot_iff,
  refine le_trans _ (le_of_eq this),
  rw ideal.jacobson,
  simp,
  introsI J j hj hJ,
  have : J.jacobson = J,
  { rw [← hJ, jacobson_eq_iff_jacobson_quotient_eq_bot],
    suffices : (⊥ : ideal (polynomial j.quotient)).jacobson = ⊥,
    {
      replace this := congr_arg (map (polynomial_quotient_equiv_quotient_polynomial j).to_ring_hom) this,
      rwa [map_jacobson_of_bijective _, map_bot] at this,
      exact (ring_equiv.bijective (polynomial_quotient_equiv_quotient_polynomial j))
    },
    rw eq_bot_iff,
    intros f hf,
    rw mem_jacobson_bot at hf,
    specialize hf (X : polynomial (j.quotient)),
    have hX : (X : polynomial j.quotient) ≠ 0 := λ hX, by simpa using congr_arg (λ f, coeff f 1) hX,
    simpa [hX] using eq_C_of_degree_eq_zero (degree_eq_zero_of_is_unit hf) },
  rw ← this,
  refine Inf_le_Inf (λ a ha, ha.right),
end


lemma six' {A B : Type*} [integral_domain A] [integral_domain B] [is_jacobson A]
  [algebra A B] (hf : function.injective (algebra_map A B))
  {a : A} (ha : a ≠ ↑0)
  (hABₐ : (((localization.of (submonoid.map (algebra_map A B : A →* B) (submonoid.powers a))).to_map.comp (algebra_map A B)).is_integral))
  : jacobson (⊥ : ideal B) = ⊥ :=
begin
  let Aₐ := localization (submonoid.powers a),
  let ϕA := localization.of (submonoid.powers a),
  let Bₐ := localization (submonoid.map (algebra_map A B : A →* B) (submonoid.powers a)),
  let ϕB := localization.of (submonoid.map (algebra_map A B : A →* B) (submonoid.powers a)),
  letI : algebra A Bₐ := (ring_hom.comp ϕB.to_map (algebra_map A B)).to_algebra,
  letI : algebra Aₐ Bₐ := localization_algebra _ ϕA ϕB,
  haveI tower : is_scalar_tower A B Bₐ :=
    is_scalar_tower.of_algebra_map_eq (λ x, ring_hom.comp_apply ϕB.to_map (algebra_map A B) x),

  have hM : (submonoid.map ↑(algebra_map A B) (submonoid.powers a)) ≤ non_zero_divisors B :=
    map_le_non_zero_divisors_of_injective hf (powers_le_non_zero_divisors_of_domain ha),
  letI : integral_domain Bₐ := localization_map.integral_domain_localization hM,
  have hϕB : function.injective ϕB.to_map := localization_map.injective ϕB hM,

  have hAB : algebra.is_integral A B := λ x, is_integral_tower_bot_of_is_integral hϕB (hABₐ _),
  have hAₐBₐ : algebra.is_integral Aₐ Bₐ := is_integral_localization ϕA ϕB hAB,
  have hBₐ : is_jacobson Bₐ := is_jacobson_of_is_integral hAₐBₐ (is_jacobson_localization ϕA),

  rw [ring_hom.injective_iff_ker_eq_bot, ring_hom.ker_eq_comap_bot] at hϕB,
  rw eq_bot_iff,
  refine le_trans _ (le_of_eq hϕB),
  rw ← hBₐ ⊥ radical_bot_of_integral_domain,
  dunfold ideal.jacobson,
  rw [comap_Inf', Inf_eq_infi],
  refine infi_le_infi_of_subset (λ j hj, ⟨bot_le, _⟩),

  cases hj with J hJ,
  haveI : J.is_maximal := hJ.1.2,
  rw ← hJ.2,
  refine is_maximal_comap_of_is_integral_of_is_maximal _ _,
  refine λ x, is_integral_tower_top_of_is_integral (hABₐ x),
end

theorem is_jacobson_polynomial_iff_is_jacobson : is_jacobson R ↔ is_jacobson (polynomial R) :=
begin
  split; introI H,
  { rw is_jacobson_iff_prime_eq,
    introsI I hI,
    rw jacobson_eq_iff_jacobson_quotient_eq_bot,
    let R' := set.range ((quotient.mk I).comp C),
    let ϕ : R →+* R' := ((quotient.mk I).comp C).cod_restrict R' (set.mem_range_self),
    have hϕ : function.surjective ϕ,
    { rintro ⟨⟨x⟩, hx⟩,
      cases hx with y hy,
      use y,
      refine subtype.eq _,
      simp,
      exact hy },
    haveI : is_subring R' := ring_hom.is_subring_set_range ((quotient.mk I).comp C),
    haveI hR' : is_jacobson R' := is_jacobson_of_surjective ⟨ϕ, hϕ⟩,
    let ϕ' : (polynomial R') →+* I.quotient := eval₂_ring_hom (is_subring.subtype R') (quotient.mk I X),
    have hϕ'_sur : function.surjective ϕ',
    { rintro ⟨f⟩,
      use eval₂ (ring_hom.comp (C : R' →+* polynomial R') ϕ) X f,
      refine polynomial.induction_on' f _ _,
      { simp_intros p q hp hq,
        rw [hp, hq] },
      { intros n a,
        rw [eval₂_monomial (C.comp ϕ), monomial_eq_smul_X, ← C_mul' a (X ^ n)],
        simp,
        refl } },
    by_cases hϕ'_inj : function.injective ϕ',
    { suffices : (⊥ : ideal (polynomial R')).jacobson = ⊥,
      { have := congr_arg (map ϕ') this,
        rwa [map_jacobson_of_bijective ⟨hϕ'_inj, hϕ'_sur⟩, map_bot] at this },
      exact bot_jacobson_polynomial (hR' ⊥ radical_bot_of_integral_domain) },
    {
      have : ∃ f ∈ (ϕ').ker, degree f > 0, {
        contrapose! hϕ'_inj,
        sorry,
      },
      rcases this with ⟨f, hfI, hf⟩,
      let a := f.leading_coeff,
      have : a ≠ 0 := sorry,
      -- refine six (is_subring.subtype R') subtype.coe_injective this _,
      sorry,
    }
  },
  { exact is_jacobson_of_surjective ⟨eval₂_ring_hom (ring_hom.id _) 1, λ x, ⟨C x, by simp⟩⟩ }
end


/-- Classical Nullstellensatz is half given by this theorem -/
lemma is_jacobson_mv_polynomial (H : is_jacobson R) (n : ℕ) :
  is_jacobson (mv_polynomial (fin n) R) :=
nat.rec_on n
  ((is_jacobson_iso
    ((mv_polynomial.ring_equiv_of_equiv R (equiv.equiv_pempty $ fin.elim0)).trans
    (mv_polynomial.pempty_ring_equiv R))).mpr H)
  (λ n hn, (is_jacobson_iso (mv_polynomial.fin_succ_equiv R n)).2 (is_jacobson_polynomial_iff_is_jacobson.1 hn))

end polynomial


end ideal
