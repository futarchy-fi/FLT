/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassIntegralGroup

/-!
# Exact equation transport on cubic groups and their affine charts

An equality of Weierstrass equations induces the identity comparison after
substitution. Its scheme map agrees with the group-object equality transport
and retains each named affine coordinate.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] {W V : WeierstrassCurve R} (h : W = V)

/-- Transport the original affine coordinate algebra along equality of equations. -/
def chartEquationMap (j : Fin 3) : Coordinate W j →ₐ[R] Coordinate V j :=
  h ▸ AlgHom.id R (Coordinate W j)

/-- Equation transport retains each of the three named coordinates. -/
theorem chartEquationMap_coord (j i : Fin 3) :
    chartEquationMap h j (coord W j i) = coord V j i := by
  subst V
  rfl

/-- Equality of the equations retains their original chart inclusions. -/
@[reassoc] theorem integralCurveChart_equation (j : Fin 3) :
    Spec.map (CommRingCat.ofHom (chartEquationMap h j).toRingHom) ≫
      integralCurveChart W j ≫ eqToHom (congrArg integralCurve h) =
        integralCurveChart V j := by
  subst V
  change Spec.map (𝟙 _) ≫ integralCurveChart W j ≫ 𝟙 _ = _
  rw [Spec.map_id, Category.id_comp, Category.comp_id]

/-- The inverse algebra transport gives the forward equation map on proper cubics. -/
@[reassoc] theorem integralCurveChart_equation_symm (j : Fin 3) :
    Spec.map (CommRingCat.ofHom (chartEquationMap h.symm j).toRingHom) ≫
      integralCurveChart V j =
        integralCurveChart W j ≫ eqToHom (congrArg integralCurve h) := by
  subst V
  change Spec.map (𝟙 _) ≫ integralCurveChart W j = integralCurveChart W j ≫ 𝟙 _
  rw [Spec.map_id, Category.id_comp, Category.comp_id]

/-- The actual group-object equality induces the same equality map of proper cubics. -/
theorem integralCurveGroup_equation_hom (hW : IsUnit W.Δ) (hV : IsUnit V.Δ)
    (hg : integralCurveGroup W hW = integralCurveGroup V hV) :
    (eqToIso hg).hom.hom.hom.hom.left = eqToHom (congrArg integralCurve h) := by
  subst V
  rfl

end FLT.Mazur.WeierstrassIntegralChart
