/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothEquationProjection

/-!
# The geometric inverse of a nodal coefficient group comparison

The full group comparison retains the original Laurent parametrization and
coefficient projection. Abstract equation transport keeps these identities
independent of the construction of the particular complete cubic.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open WeierstrassIntegralChart WeierstrassDividedDepth
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (S : Type) [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (a : Sˣ) (h : W.map (algebraMap R S) = splitNodalEquation a)

/-- The inverse coefficient comparison has its original three geometric factors. -/
theorem nodalCoefficientGroupIso_inv_left :
    ((originalSmoothCoefficientGroupIso S W).symm ≪≫
      eqToIso (congrArg integralSmoothGroup h) ≪≫
        integralSmoothSplitNodalTorusIso a).inv.hom.hom.hom.left =
    (splitNodalRelativeSmoothOverIso a).hom.left ≫
      eqToHom (congrArg (fun V => (integralSmoothOpen V).toScheme) h.symm) ≫
        (originalSmoothCoefficientIso S W).hom := by
  rw [groupIsoTriple_inv_left]
  rw [nodalGroupIso_inv, equationGroupTransport_inv_left h]
  rw [Iso.symm_inv, originalSmoothCoefficientGroupIso_hom]
  exact Category.assoc _ _ _

/-- The full nodal coefficient group comparison preserves the original whole-curve embedding. -/
@[reassoc] theorem nodalCoefficientGroupIso_inv_inclusion :
    ((originalSmoothCoefficientGroupIso S W).symm ≪≫
      eqToIso (congrArg integralSmoothGroup h) ≪≫
        integralSmoothSplitNodalTorusIso a).inv.hom.hom.hom.left ≫
      pullback.fst (integralSmoothStructure W)
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≫ (integralSmoothOpen W).ι =
    (splitNodalRelativeSmoothOverIso a).hom.left ≫ (integralSmoothOpen (splitNodalEquation a)).ι ≫
      eqToHom (congrArg integralCurve h.symm) ≫ integralCoefficientMorphism (S := S) W := by
  rw [nodalCoefficientGroupIso_inv_left S W a h]
  simp only [Category.assoc, originalSmoothCoefficientIso_fst_assoc,
    originalSmoothCoefficientMap_inclusion]
  rw [smoothEquationTransport_inclusion_assoc h.symm]

end FLT.Mazur.OneGonSmoothing
