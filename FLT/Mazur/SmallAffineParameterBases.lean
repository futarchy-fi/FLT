/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# A small choice of finitely presented affine parameter bases

The essentially small category of finitely presented affine schemes over a
fixed base supplies actual representatives. Every original affine parameter
base is isomorphic over the unchanged base to one of these representatives.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.Approximation
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Ring-coordinate affine parameter bases locally of finite presentation. -/
abbrev AffinePresentationBase (S : Scheme.{u}) :=
  MorphismProperty.CostructuredArrow @LocallyOfFinitePresentation ⊤ Scheme.Spec S

instance affinePresentationBase_essentiallySmall (S : Scheme.{u}) :
    EssentiallySmall.{u} (AffinePresentationBase S) :=
  essentiallySmall_costructuredArrow_Spec _ fun _ _ _ _ ↦ inferInstance

/-- A small type indexing actual affine parameter bases. -/
abbrev AffinePresentationIndex (S : Scheme.{u}) := SmallModel.{u} (AffinePresentationBase S)

/-- Forget ring coordinates but retain the original structure morphism. -/
def affinePresentationBaseFunctor (S : Scheme.{u}) : AffinePresentationBase S ⥤ Over S :=
  MorphismProperty.CostructuredArrow.forget _ _ _ _ ⋙ CostructuredArrow.toOver _ _

/-- The chosen representative as an actual test scheme over the original base. -/
def affinePresentationTest (S : Scheme.{u}) (i : AffinePresentationIndex S) : Over S :=
  (affinePresentationBaseFunctor S).obj ((equivSmallModel (AffinePresentationBase S)).inverse.obj i)

instance affinePresentationTest_isAffine (S : Scheme.{u}) (i : AffinePresentationIndex S) :
    IsAffine (affinePresentationTest S i).left := inferInstanceAs (IsAffine (Spec _))

instance affinePresentationTest_locallyOfFinitePresentation
    (S : Scheme.{u}) (i : AffinePresentationIndex S) :
    LocallyOfFinitePresentation (affinePresentationTest S i).hom :=
  ((equivSmallModel (AffinePresentationBase S)).inverse.obj i).prop

/-- Every original affine finitely presented parameter base has a chosen small representative. -/
theorem exists_affinePresentationTest_iso {S : Scheme.{u}} (V : Over S)
    [IsAffine V.left] [LocallyOfFinitePresentation V.hom] :
    ∃ i : AffinePresentationIndex S, Nonempty (V ≅ affinePresentationTest S i) := by
  let k := V.left.isoSpec.inv ≫ V.hom
  let A : AffinePresentationBase S := MorphismProperty.CostructuredArrow.mk ⊤ k inferInstance
  let e : V ≅ (affinePresentationBaseFunctor S).obj A :=
    Over.isoMk V.left.isoSpec (by
      change V.left.isoSpec.hom ≫ (V.left.isoSpec.inv ≫ V.hom) = V.hom
      simp)
  exact ⟨(equivSmallModel (AffinePresentationBase S)).functor.obj A,
    ⟨e ≪≫ (affinePresentationBaseFunctor S).mapIso
      ((equivSmallModel (AffinePresentationBase S)).unitIso.app A)⟩⟩

end FLT.Mazur.Approximation
