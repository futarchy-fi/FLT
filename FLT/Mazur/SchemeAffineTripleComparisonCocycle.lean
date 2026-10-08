/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossRefinementFamilyChoice
public import FLT.Mazur.SchemeAffineTripleRefinementFamily
/-!
# Effective comparison cocycle on arbitrary affine triple tests

Constructing a simultaneous faithfully flat cover proves the cocycle for the three
independently chosen canonical pair comparisons, without assuming a common cover.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X}
variable (C : Fin 3 → Chart p) {A : CommRingCat.{u}} (a : Spec A ⟶ X)
variable (f : ∀ i, (C i).baseRing ⟶ A) (w : ∀ i, Spec.map (f i) ≫ (C i).base = a)
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [∀ i, ((pullback (C i).cover).obj M).IsQuasicoherent]
attribute [local irreducible] CrossRefinement.effectiveComparison

/-- Canonical comparisons on any affine triple test satisfy the cocycle. -/
theorem commonBase_effectiveComparison_cocycle :
    (((C 0).commonBaseCrossRefinement (C 1) (f 0) (f 1)
        ((w 0).trans (w 1).symm)).effectiveComparison D).hom ≫
      (((C 1).commonBaseCrossRefinement (C 2) (f 1) (f 2)
        ((w 1).trans (w 2).symm)).effectiveComparison D).hom =
      (((C 0).commonBaseCrossRefinement (C 2) (f 0) (f 2)
        ((w 0).trans (w 2).symm)).effectiveComparison D).hom :=
  (tripleCrossRefinementFamily C a f w).canonical_effectiveComparison_cocycle D 0 1 2

end FLT.Mazur.SchemeAffineDescent.Chart
