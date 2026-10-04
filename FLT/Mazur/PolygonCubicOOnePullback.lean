/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCubicProjectiveMorphism
public import FLT.Mazur.ModuleSectionProjectiveOOne

/-!
# The actual hyperplane pullback of the polygon cubic morphism

The finite cubic sections identify the pullback of O(1) with polygonLine 3.
The comparison uses the actual pulled-back transition units and glued generator
isomorphisms. Closed immersion and relative very ampleness remain separate.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonCubicSections
open FCurve PolygonPinching PolygonPowerNodeEndpoints
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ)

/-- The cubic morphism pulls the hyperplane line back to the actual polygon cubic line. -/
def cubicProjectiveOOneIso :
    (Scheme.Modules.pullback (cubicProjectiveMorphism K n hn p q h a)).obj
      (ProjectiveSpace.O K (n * 3 + 1) 1) ≅ polygonLine K n hn p q h a 3 :=
  sectionProjectiveOOneIso (polygonLine K n hn p q h a 3) (n * 3 + 1)
    (finiteCubicFamily K n hn p q h a) (iSup_finiteCubicOpen K n hn p q h a)
    (C.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)

end FLT.Mazur.PolygonCubicSections
