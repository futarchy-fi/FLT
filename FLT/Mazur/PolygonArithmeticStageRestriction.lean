/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticStageFamilies
public import FLT.Mazur.PolygonParameterProjectionComposition

/-!
# Cartesian restrictions of the original arithmetic smoothing stages

The restrictions A/(π^(m+2)) → A/(π^(m+1)) give actual Cartesian
family maps. They preserve the original markings and commute with the
specified specializations from the universal integral-coefficient stages.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonArithmeticStages
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (A : Type u) [CommRing A] (π : A) (m n : ℕ) (h : 2 ≤ n)

/-- The original adjacent restriction on arithmetic coefficient spectra. -/
def baseRestriction : Spec (.of (Quotient A π m)) ⟶ Spec (.of (Quotient A π (m + 1))) :=
  Spec.map (CommRingCat.ofHom (restriction A π m).toRingHom)

/-- Restriction of the complete cyclic family to the smaller arithmetic thickening. -/
def stageRestriction : (family A π m n h).left ⟶ (family A π (m + 1) n h).left :=
  PolygonInfinitesimal.parameterProjection (restriction A π m).toRingHom
    (parameter A π (m + 1)) (parameter A π m) (restriction_parameter A π m) n h

/-- Every adjacent restriction is an actual Cartesian square of families. -/
theorem stageRestriction_isPullback :
    IsPullback (stageRestriction A π m n h) (family A π m n h).hom
      (family A π (m + 1) n h).hom (baseRestriction A π m) :=
  PolygonInfinitesimal.parameterProjection_isPullback _ _ _
    (restriction_parameter A π m) n h

/-- Restriction retains the original arithmetic structure morphism. -/
@[reassoc] theorem stageRestriction_base :
    stageRestriction A π m n h ≫ (family A π (m + 1) n h).hom =
      (family A π m n h).hom ≫ baseRestriction A π m :=
  (stageRestriction_isPullback A π m n h).w

/-- Each original unit-one marking is compatible with adjacent arithmetic restriction. -/
@[reassoc] theorem marking_stageRestriction (i : Fin n) :
    marking A π m n h i ≫ stageRestriction A π m n h =
      baseRestriction A π m ≫ marking A π (m + 1) n h i := by
  simpa only [map_one, marking, stageRestriction, baseRestriction] using
    PolygonInfinitesimal.marking_parameterProjection
    (restriction A π m).toRingHom (parameter A π (m + 1)) (parameter A π m)
    (restriction_parameter A π m) n h i 1

/-- Specialization commutes with the actual adjacent coefficient inclusions. -/
@[reassoc] theorem baseRestriction_specialization :
    baseRestriction A π m ≫ specializationBase A π (m + 1) =
      specializationBase A π m ≫ PolygonInfinitesimalStages.baseRestriction A m := by
  simp only [baseRestriction, specializationBase, PolygonInfinitesimalStages.baseRestriction,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f : PolygonInfinitesimalStages.Ring A (m + 1) →ₐ[A] Quotient A π m ↦
    Spec.map (CommRingCat.ofHom f.toRingHom)) (restriction_specialization A π m)

/-- Specialization commutes on the entire family, including all original node charts. -/
@[reassoc] theorem stageRestriction_specialization :
    stageRestriction A π m n h ≫ specializationFamily A π (m + 1) n h =
      specializationFamily A π m n h ≫ PolygonInfinitesimalStages.stageRestriction A m n h := by
  simp only [stageRestriction, specializationFamily, PolygonInfinitesimalStages.stageRestriction,
    PolygonInfinitesimal.parameterProjection_comp]
  congr 1
  exact congrArg AlgHom.toRingHom (restriction_specialization A π m)

end FLT.Mazur.PolygonArithmeticStages
