/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossRefinement

/-!
# Base change of faithfully flat affine charts

The ring pushout constructs the covering ring over any new affine base.
Faithful flatness is preserved, and its spectrum is the geometric pullback.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
variable {X Y : Scheme.{u}} {p : Y ⟶ X} (C : Chart p)
variable {A : CommRingCat.{u}} (f : C.baseRing ⟶ A)

/-- The pushout covering ring remains faithfully flat over the new base. -/
theorem baseChange_faithfullyFlat :
    (pushout.inl f C.ringMap).hom.FaithfullyFlat :=
  RingHom.FaithfullyFlat.isStableUnderBaseChange.pushout_inl
    RingHom.FaithfullyFlat.respectsIso f C.ringMap C.faithfullyFlat

/-- The base-changed chart is built from the actual ring pushout. -/
def baseChange : Chart p where
  baseRing := A
  coverRing := pushout f C.ringMap
  ringMap := pushout.inl f C.ringMap
  faithfullyFlat := C.baseChange_faithfullyFlat f
  base := Spec.map f ≫ C.base
  cover := Spec.map (pushout.inr f C.ringMap) ≫ C.cover
  square := SchemeGeometricDescent.Data.affineChart_composite_square
    C.ringMap (pushout.inl f C.ringMap) f (pushout.inr f C.ringMap)
    (pushout.condition.symm) p C.base C.cover C.square

/-- The constructed base change refines the original geometric chart. -/
def baseChangeRefinement : C.Refinement (C.baseChange f) where
  base := f
  cover := pushout.inr f C.ringMap
  square := pushout.condition.symm
  base_over := rfl
  cover_over := rfl

/-- The new affine covering scheme is the pullback of the original affine cover. -/
theorem baseChange_isPullback :
    IsPullback (Spec.map (C.baseChange f).ringMap)
      (Spec.map (C.baseChangeRefinement f).cover) (Spec.map f) (Spec.map C.ringMap) :=
  isPullback_SpecMap_pushout f C.ringMap

end FLT.Mazur.SchemeAffineDescent.Chart
