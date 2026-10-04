/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCubicProjectiveMorphism
public import FLT.Mazur.ModuleSectionProjectiveOver

/-!
# The polygon cubic morphism over its base field

The structural coefficient map in the chart construction makes the glued
projective-space morphism commute with the actual polygon map to Spec K.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonCubicSections
open FCurve PolygonPinching PolygonPowerNodeEndpoints
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ)

/-- The actual cubic projective morphism is a morphism over Spec K. -/
@[reassoc] lemma cubicProjectiveMorphism_baseProjection :
    cubicProjectiveMorphism K n hn p q h a ≫
      ProjectiveSpace.baseProjection K (Fin (n * 3 + 1 + 1)) = C.hom :=
  sectionProjectiveMorphism_baseProjection (polygonLine K n hn p q h a 3) (n * 3 + 1)
    (finiteCubicFamily K n hn p q h a) (iSup_finiteCubicOpen K n hn p q h a) C.hom

end FLT.Mazur.PolygonCubicSections
