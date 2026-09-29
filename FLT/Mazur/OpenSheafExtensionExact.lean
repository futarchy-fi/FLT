/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenSheafExtensionStalks
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Exact extension from an open subspace

The inside stalk comparison is natural in the coefficient sheaf. Exactness
therefore follows from exactness on stalks inside the open and zero stalks
outside it. The extension-restriction adjunction then shows that restriction
preserves injective objects.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor TopologicalSpace Opposite
open TopCat.Presheaf

universe u

namespace FLT.Mazur.OpenSheafRestriction

variable {X : TopCat.{u}} (W : Opens X)

/-- The restriction comparison commutes with maps of presheaves. -/
@[reassoc]
lemma restrictionPresheafStalkIso_naturality {P Q : X.Presheaf AddCommGrpCat.{u}}
    (f : P ⟶ Q) (x : W) :
    (stalkFunctor AddCommGrpCat.{u} x.val).map f ≫
        (restrictionPresheafStalkIso W Q x).hom =
      (restrictionPresheafStalkIso W P x).hom ≫
        (stalkFunctor (X := TopCat.of W) AddCommGrpCat.{u} x).map
          (whiskerLeft (openImage W).op f) := by
  have h : (stalkFunctor AddCommGrpCat.{u} x.val).map f ≫
      (stalkPullbackIso AddCommGrpCat.{u} (inclusion W) Q x).hom =
    (stalkPullbackIso AddCommGrpCat.{u} (inclusion W) P x).hom ≫
      (stalkFunctor AddCommGrpCat.{u} x).map
        ((pullback AddCommGrpCat.{u} (inclusion W)).map f) := by
    change (stalkFunctor AddCommGrpCat.{u} ((inclusion W) x)).map f ≫
        stalkPullbackHom AddCommGrpCat.{u} (inclusion W) Q x =
      stalkPullbackHom AddCommGrpCat.{u} (inclusion W) P x ≫ _
    apply stalk_hom_ext
    intro V hx
    rw [stalkFunctor_map_germ_assoc, germ_stalkPullbackHom,
      germ_stalkPullbackHom_assoc, stalkFunctor_map_germ]
    rw [← Category.assoc, ← Category.assoc]
    exact congrArg (fun t ↦ t.app (op V) ≫ _)
      ((pullbackPushforwardAdjunction AddCommGrpCat.{u} (inclusion W)).unit.naturality f)
  dsimp only [restrictionPresheafStalkIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, h]
  simp only [Category.assoc, ← Functor.map_comp]
  exact congrArg (fun t ↦ (stalkPullbackIso AddCommGrpCat.{u}
    (inclusion W) P x).hom ≫ (stalkFunctor AddCommGrpCat.{u} x).map t)
    ((IsOpenMap.pullbackIso (C := AddCommGrpCat.{u})
      (W.isOpenEmbedding.isOpenMap : IsOpenMap (inclusion W))).hom.naturality f)

/-- The presheaf extension's inside stalk comparison is natural. -/
@[reassoc]
lemma extensionPresheafStalkIso_naturality
    {P Q : (TopCat.of W).Presheaf AddCommGrpCat.{u}} (f : P ⟶ Q) (x : W) :
    (stalkFunctor AddCommGrpCat.{u} x.val).map ((extensionPresheaf W).map f) ≫
        (extensionPresheafStalkIso W Q x).hom =
      (extensionPresheafStalkIso W P x).hom ≫
        (stalkFunctor AddCommGrpCat.{u} x).map f := by
  dsimp only [extensionPresheafStalkIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← Category.assoc, restrictionPresheafStalkIso_naturality]
  simp only [Category.assoc, ← Functor.map_comp]
  congr 2
  apply (cancel_epi ((presheafAdjunction W).unit.app P)).mp
  simp only [← Category.assoc, asIso_inv, IsIso.hom_inv_id, Category.id_comp]
  rw [show (presheafAdjunction W).unit.app P ≫
      whiskerLeft (openImage W).op ((extensionPresheaf W).map f) =
      f ≫ (presheafAdjunction W).unit.app Q from
    ((presheafAdjunction W).unit.naturality f).symm]
  simp

/-- The sheaf extension's inside stalk comparison is natural. -/
@[reassoc]
lemma extensionStalkIso_naturality
    {F G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of W)} (f : F ⟶ G) (x : W) :
    (stalkFunctor AddCommGrpCat.{u} x.val).map ((extension W).map f).hom ≫
        (extensionStalkIso W G x).hom =
      (extensionStalkIso W F x).hom ≫
        (stalkFunctor AddCommGrpCat.{u} x).map f.hom := by
  dsimp only [extensionStalkIso, Iso.trans_hom, Iso.symm_hom]
  apply (cancel_epi (extensionSheafifyStalkIso W F x.val).hom).mp
  simp only [← Category.assoc]
  rw [← extensionSheafifyStalkIso_naturality]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact extensionPresheafStalkIso_naturality W f.hom x

instance extension_additive : (extension W).Additive :=
  (rightExactFunctor_le_additiveFunctor _ _) _ (by
    rw [rightExactFunctor_iff]
    infer_instance)

/-- Extension carries exact short complexes to exact short complexes. -/
lemma extension_map_exact (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of W)))
    (hS : S.Exact) : (S.map (extension W)).Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).mpr
  intro x
  by_cases hx : x ∈ W
  · let y : W := ⟨x, hx⟩
    let e : (S.map (extension W)).map
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ stalkFunctor AddCommGrpCat.{u} x) ≅
        S.map (TopCat.Sheaf.forget AddCommGrpCat.{u} (TopCat.of W) ⋙
          stalkFunctor (X := TopCat.of W) AddCommGrpCat.{u} y) :=
      ShortComplex.isoMk (extensionStalkIso W S.X₁ y) (extensionStalkIso W S.X₂ y)
        (extensionStalkIso W S.X₃ y)
        (extensionStalkIso_naturality W S.f y).symm
        (extensionStalkIso_naturality W S.g y).symm
    exact ShortComplex.exact_of_iso e.symm
      ((TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S).mp hS y)
  · exact ShortComplex.exact_of_isZero_X₂ _ (extensionStalk_isZero W S.X₂ x hx)

instance extension_preservesHomology : (extension W).PreservesHomology :=
  preservesHomology_of_map_exact _ (extension_map_exact W)

instance extension_preservesFiniteLimits : PreservesFiniteLimits (extension W) :=
  (extension W).preservesFiniteLimits_of_preservesHomology

instance restriction_preservesInjectiveObjects :
    (restriction W).PreservesInjectiveObjects :=
  preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms (adjunction W)

/-- Restriction to an open sends an injective sheaf to an injective sheaf. -/
lemma restriction_injective (I : TopCat.Sheaf AddCommGrpCat.{u} X) [Injective I] :
    Injective ((restriction W).obj I) := inferInstance

end FLT.Mazur.OpenSheafRestriction
