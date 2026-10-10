/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineImageTestComparison

/-!
# Coordinate-independent refinement of image-open comparisons

Monicity identifies independently chosen coordinates of a smaller common test.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
open ModuleSheafMorphismGluing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y W Z : Scheme.{u}} {p : Y ⟶ X} (C C' : Chart p)
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]
variable [IsOpenImmersion C.base] [IsOpenImmersion C'.base]
attribute [local irreducible] sheaf imageTestComparison

/-- Refinement is independent of presentations of the smaller test's coordinates. -/
theorem imageTestComparison_refine_of_eq (t : Z ⟶ W) (a : W ⟶ X) (a' : Z ⟶ X)
    [IsOpenImmersion t] [IsOpenImmersion a] [IsOpenImmersion a'] (ha : t ≫ a = a')
    (i : W ⟶ Spec C.baseRing) (j : W ⟶ Spec C'.baseRing)
    (hi : i ≫ C.base = a) (hj : j ≫ C'.base = a)
    (i' : Z ⟶ Spec C.baseRing) (j' : Z ⟶ Spec C'.baseRing)
    (hi' : i' ≫ C.base = a') (hj' : j' ≫ C'.base = a')
    (U : X.Opens) (hU : U ≤ a'.opensRange) (hA : U ≤ a.opensRange) :
    localApp (C.imageTestComparison C' D a' i' j' hi' hj') hU =
      localApp (C.imageTestComparison C' D a i j hi hj) hA := by
  subst a'
  have ei : i' = t ≫ i := by
    apply (cancel_mono C.base).mp
    rw [hi', Category.assoc, hi]
  have ej : j' = t ≫ j := by
    apply (cancel_mono C'.base).mp
    rw [hj', Category.assoc, hj]
  subst i' j'
  exact C.imageTestComparison_refine C' D t a i j hi hj U hU hA

end FLT.Mazur.SchemeAffineDescent.Chart
