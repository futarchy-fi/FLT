/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassNodalResidueTransition
public import FLT.Mazur.WeierstrassIntegralCoefficientMap

/-!
# The original projective cubic contraction of the nodal residue equation

Equation transport followed by the actual coefficient morphism retains every
original cubic function on each normalized chart of the whole nodal cubic.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {S : Type u} [CommRing S] {U V : WeierstrassCurve S}

/-- Equal equations give equal glued projective cubics. -/
def equationCurveIso (h : U = V) : integralCurve U ≅ integralCurve V := h ▸ Iso.refl _

/-- Equation transport retains every original chart inclusion. -/
@[reassoc] theorem equationCurveIso_chart (h : U = V) (j : Fin 3) :
    integralCurveChart V j ≫ (equationCurveIso h).inv =
      (Scheme.Spec.mapIso (equationChartEquiv h j).toRingEquiv.toCommRingCatIso.op).hom ≫
        integralCurveChart U j := by
  subst V
  simp [equationCurveIso, equationChartEquiv]

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hdepth : 0 < depth)
local notation "K" => ResidueField R
local notation "N" => splitNodalEquation (WeierstrassDilatation.residueTangentUnit D)

/-- The nodal chart map is coefficient reduction followed by equation transport. -/
theorem nodalResidueChartMap_coefficient (j : Fin 3) :
    nodalResidueChartMap D hdepth j =
      ((equationChartEquiv (splitDepth_residue_equation D hdepth) j).toAlgHom.restrictScalars
        R).comp (chartCoefficientMap W j) := by
  apply hom_ext
  intro i
  rw [nodalResidueChartMap_coord, AlgHom.comp_apply, chartCoefficientMap_coord]
  exact (equationChartEquiv_coord (splitDepth_residue_equation D hdepth) j i).symm

/-- The full nodal projective cubic contracts by the original coefficient reduction. -/
def nodalResidueContraction : integralCurve N ⟶ integralCurve W :=
  (equationCurveIso (splitDepth_residue_equation D hdepth)).inv ≫
    integralCoefficientMorphism W

/-- The full projective contraction retains every original chart function. -/
@[reassoc] theorem integralCurveChart_nodalResidueContraction (j : Fin 3) :
    integralCurveChart N j ≫ nodalResidueContraction D hdepth =
      Spec.map (CommRingCat.ofHom (nodalResidueChartMap D hdepth j).toRingHom) ≫
        integralCurveChart W j := by
  rw [nodalResidueContraction, equationCurveIso_chart_assoc,
    integralCurveChart_coefficientMorphism, ← Category.assoc, nodalResidueChartMap_coefficient]
  change (Spec.map _ ≫ Spec.map _) ≫ _ = Spec.map _ ≫ _
  rw [← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassIntegralChart
