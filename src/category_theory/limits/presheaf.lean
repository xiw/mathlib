/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.adjunction
import category_theory.elements
import category_theory.limits.functor_category
import category_theory.limits.shapes
import category_theory.limits.types
import category_theory.limits.shapes.types
import category_theory.closed.cartesian
import category_theory.conj

/-!
# Colimit of representables

This file constructs an adjunction between `(Cᵒᵖ ⥤ Type u)` and `ℰ` given a functor `A : C ⥤ ℰ`,
where the right adjoint sends `(E : ℰ)` to `c ↦ (A.obj c ⟶ E)` (provided `ℰ` has colimits).

This adjunction is used to show that every presheaf is a colimit of representables.

Further, the left adjoint `colimit_adj.L : (Cᵒᵖ ⥤ Type u) ⥤ ℰ` satisfies `yoneda ⋙ L ≅ A`, that
is, an extension of `A : C ⥤ ℰ` to `(Cᵒᵖ ⥤ Type u) ⥤ ℰ` through `yoneda : C ⥤ Cᵒᵖ ⥤ Type u`.
TODO: Show `colimit_adj.L` is unique amongst cocontinuous functors with this property.

## Tags
colimit, representable, presheaf
-/

namespace category_theory

noncomputable theory

open category limits
universes u₁ u₂

variables {C : Type u₁} [small_category C]
variables {ℰ : Type u₂} [category.{u₁} ℰ]
variable (A : C ⥤ ℰ)

namespace colimit_adj

/--
The functor taking `(E : ℰ) (c : Cᵒᵖ)` to the homset `(A.obj C ⟶ E)`. It is shown in `L_adjunction`
that this functor has a left adjoint (provided `E` has colimits) given by taking colimits over
categories of elements.
In the case where `ℰ = Cᵒᵖ ⥤ Type u` and `A = yoneda`, this functor is isomorphic to the identity.

Defined as in [MM92], Chapter I, Section 5, Theorem 2.
-/
@[simps {rhs_md := semireducible}]
def restricted_yoneda : ℰ ⥤ (Cᵒᵖ ⥤ Type u₁) :=
yoneda ⋙ (whiskering_left _ _ (Type u₁)).obj (functor.op A)

/--
The functor `restricted_yoneda` is isomorphic to the identity functor when evaluated at the yoneda
embedding.
-/
def restricted_yoneda_yoneda : restricted_yoneda (yoneda : C ⥤ Cᵒᵖ ⥤ Type u₁) ≅ 𝟭 _ :=
nat_iso.of_components
(λ P, nat_iso.of_components (λ X, yoneda_sections_small X.unop _)
  (λ X Y f, funext $ λ x,
  begin
    dsimp [ulift_trivial, yoneda_lemma],
    rw ← functor_to_types.naturality _ _ x f (𝟙 _),
    dsimp,
    simp,
  end))
(λ _ _ _, rfl)

/--
(Implementation). The equivalence of homsets which helps construct the left adjoint to
`colimit_adj.restricted_yoneda`.
It is shown in `restrict_yoneda_hom_equiv_natural` that this is a natural bijection.
-/
def restrict_yoneda_hom_equiv (P : Cᵒᵖ ⥤ Type u₁) (E : ℰ)
  {c : cocone ((category_of_elements.π P).left_op ⋙ A)} (t : is_colimit c) :
  (c.X ⟶ E) ≃ (P ⟶ (restricted_yoneda A).obj E) :=
(t.hom_iso' E).to_equiv.trans
{ to_fun := λ k,
  { app := λ c p, k.1 (opposite.op ⟨_, p⟩),
    naturality' := λ c c' f, funext $ λ p,
      (k.2 (has_hom.hom.op ⟨f, rfl⟩ :
              (opposite.op ⟨c', P.map f p⟩ : P.elementsᵒᵖ) ⟶ opposite.op ⟨c, p⟩)).symm },
  inv_fun := λ τ,
  { val := λ p, τ.app p.unop.1 p.unop.2,
    property := λ p p' f,
    begin
      simp_rw [← f.unop.2],
      apply (congr_fun (τ.naturality f.unop.1) p'.unop.2).symm,
    end },
  left_inv :=
  begin
    rintro ⟨k₁, k₂⟩,
    ext,
    dsimp,
    congr' 1,
    simp,
  end,
  right_inv :=
  begin
    rintro ⟨_, _⟩,
    refl,
  end }

/-- (Implementation). Show that the bijection in `Le'` is natural (on the right). -/
lemma restrict_yoneda_hom_equiv_natural (P : Cᵒᵖ ⥤ Type u₁) (E₁ E₂ : ℰ) (g : E₁ ⟶ E₂)
  {c : cocone _} (t : is_colimit c) (k : c.X ⟶ E₁) :
restrict_yoneda_hom_equiv A P E₂ t (k ≫ g) =
  restrict_yoneda_hom_equiv A P E₁ t k ≫ (restricted_yoneda A).map g :=
begin
  ext _ X p,
  apply (assoc _ _ _).symm,
end

variables [has_colimits ℰ]

/--
The left adjoint to the functor `restricted_yoneda` (shown in `yoneda_adjunction`). It is also an
extension of `A` along the yoneda embedding (shown in `is_extension_along_yoneda`). -/
def extend_along_yoneda : (Cᵒᵖ ⥤ Type u₁) ⥤ ℰ :=
adjunction.left_adjoint_of_equiv
  (λ P E, restrict_yoneda_hom_equiv A P E (colimit.is_colimit _))
  (λ P E E' g, restrict_yoneda_hom_equiv_natural A P E E' g _)

@[simp]
lemma extend_along_yoneda_obj (P : Cᵒᵖ ⥤ Type u₁) : (extend_along_yoneda A).obj P =
colimit ((category_of_elements.π P).left_op ⋙ A) := rfl

/--
Show `extend_along_yoneda` is left adjoint to `restricted_yoneda`.

The construction of [MM92], Chapter I, Section 5, Theorem 2.
-/
def yoneda_adjunction : extend_along_yoneda A ⊣ restricted_yoneda A :=
adjunction.adjunction_of_equiv_left _ _

/--
The initial object in the category of elements for a representable functor. In `is_initial` it is
shown that this is terminal.
-/
def elements.initial (A : C) : (yoneda.obj A).elements :=
⟨opposite.op A, 𝟙 _⟩

/--
Show that `elements.initial A` is initial in the category of elements for the `yoneda` functor.
-/
def is_initial (A : C) : is_initial (elements.initial A) :=
{ desc := λ s, ⟨s.X.2.op, comp_id _⟩,
  uniq' := λ s m w,
  begin
    simp_rw ← m.2,
    dsimp [elements.initial],
    simp,
  end }

/--
`extend_along_yoneda A` is an extension of `A` to the presheaf category along the yoneda embedding.
TODO: Among functors preserving colimits, `extend_along_yoneda` is unique with this property (up to
isomorphism).

The first part of [MM92], Chapter I, Section 5, Corollary 4.
-/
def is_extension_along_yoneda : (yoneda : C ⥤ Cᵒᵖ ⥤ Type u₁) ⋙ extend_along_yoneda A ≅ A :=
nat_iso.of_components
(λ X, (colimit.is_colimit _).cocone_point_unique_up_to_iso
      (colimit_of_diagram_terminal (terminal_op_of_initial (is_initial _)) _))
begin
  intros X Y f,
  change (colimit.desc _ ⟨_, _⟩ ≫ colimit.desc _ _) = colimit.desc _ _ ≫ _,
  apply colimit.hom_ext,
  intro j,
  rw [colimit.ι_desc_assoc, colimit.ι_desc_assoc],
  change (colimit.ι _ _ ≫ 𝟙 _) ≫ colimit.desc _ _ = _,
  rw [comp_id, colimit.ι_desc],
  dsimp,
  rw ← A.map_comp,
  congr' 1,
end

end colimit_adj

open colimit_adj

/--
Since `extend_along_yoneda A` is adjoint to `restricted_yoneda A`, if we use `A = yoneda`
then `restricted_yoneda A` is isomorphic to the identity, and so `extend_along_yoneda A` is as well.
-/
def extend_along_yoneda_yoneda : extend_along_yoneda (yoneda : C ⥤ _) ≅ 𝟭 _ :=
adjunction.nat_iso_of_right_adjoint_nat_iso
  (yoneda_adjunction _)
  adjunction.id
  restricted_yoneda_yoneda

/--
This is a cocone with point `P`, for which the diagram consists solely of representables.
It is shown in `colimit_of_representable P` that this cocone is a colimit: that is, we have
exhibited an arbitrary presheaf `P` as a colimit of representables.

The construction of [MM92], Chapter I, Section 5, Corollary 3.
-/
def cocone_of_representable (P : Cᵒᵖ ⥤ Type u₁) :
  cocone ((category_of_elements.π P).left_op ⋙ yoneda) :=
cocone.extend (colimit.cocone _) (extend_along_yoneda_yoneda.hom.app P)

@[simp] lemma cocone_of_representable_X (P : Cᵒᵖ ⥤ Type u₁) : (cocone_of_representable P).X = P := rfl

/--
The cocone with point `P` given by `the_cocone` is a colimit: that is, we have exhibited an
arbitrary presheaf `P` as a colimit of representables.

The result of [MM92], Chapter I, Section 5, Corollary 3.
-/
def colimit_of_representable (P : Cᵒᵖ ⥤ Type u₁) : is_colimit (cocone_of_representable P) :=
begin
  apply is_colimit.of_point_iso (colimit.is_colimit ((category_of_elements.π P).left_op ⋙ yoneda)),
  change is_iso (colimit.desc _ (cocone.extend _ _)),
  rw [colimit.desc_extend, colimit.desc_cocone],
  apply_instance,
end

section cartesian_closed

universes v₃ u₃
variables {D : Type u₃} [category.{u₁} D]

instance [has_finite_products D] [cartesian_closed D] (X : D) :
  preserves_colimits (prod.functor.obj X) :=
(exp.adjunction X).left_adjoint_preserves_colimits

instance prod_preserves_colimits [has_finite_products D] [cartesian_closed D] [has_colimits D]
  (F : C ⥤ D) :
  preserves_colimits (prod.functor.obj F) :=
{ preserves_colimits_of_shape := λ J 𝒥, by exactI
  { preserves_colimit := λ K,
    { preserves := λ c t,
      begin
        apply evaluation_jointly_reflects_colimits,
        intro k,
        change is_colimit ((prod.functor.obj F ⋙ (evaluation _ _).obj k).map_cocone c),
        let i : (prod.functor.obj F ⋙ (evaluation C D).obj k) ≅ ((evaluation C D).obj k ⋙ prod.functor.obj (F.obj k)),
          apply nat_iso.of_components _ _,
          { intro G,
            apply as_iso (prod_comparison ((evaluation C D).obj k) F G) },
          { intros G G' z,
            apply prod_comparison_natural ((evaluation C D).obj k) (𝟙 F) z },
        let i' : K ⋙ (prod.functor.obj F ⋙ (evaluation C D).obj k) ≅ K ⋙ (evaluation C D).obj k ⋙ prod.functor.obj (F.obj k),
          apply iso_whisker_left K i,
        let : is_colimit (((evaluation C D).obj k ⋙ prod.functor.obj (F.obj k)).map_cocone c),
          apply preserves_colimit.preserves,
          apply t,
        apply is_colimit.of_iso_colimit ((is_colimit.precompose_hom_equiv i' _).symm this),
        apply cocones.ext _ _,
          apply (as_iso (prod_comparison ((evaluation C D).obj k) F c.X)).symm,
        intro j,
        dsimp,
        rw is_iso.comp_inv_eq,
        apply (prod_comparison_natural ((evaluation C D).obj k) (𝟙 F) (c.ι.app j)).symm,
      end } } }

@[simps]
def presheaf_exp (F G : Cᵒᵖ ⥤ Type u₁) : Cᵒᵖ ⥤ Type u₁ :=
{ obj := λ A, F ⨯ yoneda.obj A.unop ⟶ G,
  map := λ A B f α, limits.prod.map (𝟙 _) (yoneda.map f.unop) ≫ α }.

def presheaf_exp_representable_hom_equiv (F G : Cᵒᵖ ⥤ Type u₁) (A : C) :
  (yoneda.obj A ⟶ presheaf_exp F G) ≃ (F ⨯ yoneda.obj A ⟶ G) :=
(yoneda_sections_small A (presheaf_exp F G)).to_equiv

@[simp]
lemma yoneda_sections_small_hom_apply (X : C) (F f) :
  (yoneda_sections_small X F).hom f = f.app _ (𝟙 _) :=
rfl

@[simp]
lemma yoneda_sections_small_inv (X : C) (F t) (Y : Cᵒᵖ) (f : Y.unop ⟶ X) :
  ((yoneda_sections_small X F).inv t).app Y f = F.map f.op t :=
rfl

lemma presheaf_exp_representable_hom_equiv_symm_natural_A (F G : Cᵒᵖ ⥤ Type u₁)
  {A B : C} (g : B ⟶ A) (f : F ⨯ yoneda.obj A ⟶ G) :
  yoneda.map g ≫ (presheaf_exp_representable_hom_equiv F G A).symm f =
  (presheaf_exp_representable_hom_equiv F G B).symm (limits.prod.map (𝟙 _) (yoneda.map g) ≫ f) :=
begin
  ext a h b : 3,
  simp only [yoneda_map_app, functor_to_types.comp],
  change ((yoneda_sections_small A (presheaf_exp F G)).inv f).app a (h ≫ g) =
    (((presheaf_exp_representable_hom_equiv F G B).symm) (limits.prod.map (𝟙 F) (yoneda.map g) ≫ f)).app a h,
  change ((yoneda_sections_small A (presheaf_exp F G)).inv f).app a (h ≫ g) =
    (((yoneda_sections_small B (presheaf_exp F G)).inv) (limits.prod.map (𝟙 F) (yoneda.map g) ≫ f)).app a h,
  rw yoneda_sections_small_inv,
  rw yoneda_sections_small_inv,
  simp,
end

lemma presheaf_exp_representable_hom_equiv_natural_A (F G : Cᵒᵖ ⥤ Type u₁)
  {A B : C} (g : B ⟶ A) (f) :
  (presheaf_exp_representable_hom_equiv F G B) (yoneda.map g ≫ f) =
  (limits.prod.map (𝟙 _) (yoneda.map g) ≫ presheaf_exp_representable_hom_equiv F G A f) :=
begin
  rw ← equiv.eq_symm_apply,
  rw ← presheaf_exp_representable_hom_equiv_symm_natural_A,
  rw equiv.symm_apply_apply,
end

instance : has_finite_products (Type u₁) := has_finite_products_of_has_products _

def type_equiv {X Y Z : Type u₁} : (Z × X ⟶ Y) ≃ (X → (Z → Y)) :=
{ to_fun := λ f x z, f ⟨z, x⟩,
  inv_fun := λ f ⟨z, x⟩, f x z,
  left_inv := λ f, funext (λ ⟨z, x⟩, rfl),
  right_inv := λ x, rfl }

def type_equiv' {X Y Z : Type u₁} : (Z ⨯ X ⟶ Y) ≃ (X → (Z → Y)) :=
begin
  apply equiv.trans _ type_equiv,
  apply iso.hom_congr _ (iso.refl _),
  apply limit.iso_limit_cone (types.binary_product_limit_cone _ _),
end

lemma type_equiv'_natural {X X' Y Z : Type u₁} (f : X' ⟶ X) (g : Z ⨯ X ⟶ Y) :
  type_equiv' (limits.prod.map (𝟙 Z) f ≫ g) = f ≫ type_equiv' g :=
begin
  dsimp [type_equiv'],
  have := types.binary_product_limit_cone Z X,
  -- ext x' z,
  -- rw type_equiv',
  -- dsimp,
  -- dsimp only [iso.hom_congr],

  -- dsimp [type_equiv'],
  -- rw comp_id,
  -- rw comp_id,
  -- have := limit.iso_limit_cone_inv_π,

end

instance : cartesian_closed (Type u₁) :=
{ closed := λ Z,
  { is_adj :=
    { right :=
      begin
        refine @adjunction.right_adjoint_of_equiv _ _ _ _ (prod.functor.obj Z) _ (λ X Y, type_equiv') _,
        intros X' X Y f g,
        dsimp,
      end,
      adj :=
      begin
        refine @adjunction.adjunction_of_equiv_right _ _ _ _ (prod.functor.obj Z) _ (λ X Y, type_equiv') _,
      end
    }

  }

}

-- set_option pp.universes true

def presheaf_exp_hom_equiv (F G H : Cᵒᵖ ⥤ Type u₁) : (H ⟶ presheaf_exp F G) ≃ (F ⨯ H ⟶ G) :=
begin
  let : is_colimit ((prod.functor.obj F).map_cocone (cocone_of_representable H)),
    apply preserves_colimit.preserves,
    apply colimit_of_representable,
  apply iso.to_equiv,
  apply ((colimit_of_representable H).hom_iso (presheaf_exp F G)) ≪≫ _ ≪≫ (this.hom_iso G).symm,
  apply equiv.to_iso,
  refine ⟨_, _, _, _⟩,
  { intro f,
    refine ⟨λ X, presheaf_exp_representable_hom_equiv _ _ _ (f.app X), _⟩,
    intros X Y g,
    dsimp,
    rw ← presheaf_exp_representable_hom_equiv_natural_A,
    have h₁ := f.naturality g,
    dsimp at h₁,
    rw [h₁, comp_id, comp_id] },
  { intro f,
    refine ⟨λ X, (presheaf_exp_representable_hom_equiv _ _ _).symm (f.app X), _⟩,
    intros X Y g,
    dsimp,
    have h₁ : limits.prod.map (𝟙 F) (yoneda.map (g.unop : Y.unop.1 ⟶ X.unop.1).unop) ≫ f.app Y = f.app X ≫ 𝟙 G,
      apply f.naturality g,
    rw presheaf_exp_representable_hom_equiv_symm_natural_A,
    rw h₁,
    dsimp, simp },
  { intro f,
    ext : 2,
    dsimp,
    simp },
  { intro f,
    ext : 2,
    dsimp,
    simp }
end

-- calc (H ⟶ presheaf_exp F G) ≃ ((cocone_of_representable H).X ⟶ presheaf_exp F G) : equiv.refl _
--                         ... ≃ (((category_of_elements.π H).left_op ⋙ yoneda) ⟶ (functor.const _).obj (presheaf_exp F G)) : (colimit_of_representable H).hom_iso _
--                         ... ≃ (F ⨯ H ⟶ G) : sorry
-- { to_fun := λ g,
--   begin

--   end,
--   inv_fun := λ f,
--   begin
--     let Q : cocone ((category_of_elements.π H).left_op ⋙ yoneda),
--     { refine ⟨presheaf_exp F G, _, _⟩,
--       { intro X,
--         apply (presheaf_exp_representable_hom_equiv F G _).symm _,
--         apply limits.prod.map (𝟙 _) _ ≫ f,
--         apply (cocone_of_representable H).ι.app X },
--       { intros X Y g,
--         dsimp,
--         rw comp_id,
--         rw ← (cocone_of_representable H).w g,
--         dsimp,
--         rw presheaf_exp_representable_hom_equiv_symm_natural_A,
--         rw [prod.map_map_assoc, comp_id] } },
--     apply (colimit_of_representable H).desc Q,
--   end,

-- }
-- begin
--   change ((cocone_of_representable H).X ⟶ _) ≃ _,
-- end

end cartesian_closed

end category_theory
