/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonNodalCoefficientGroupMap

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

/-- A specified coefficient group comparison retains its geometric inverse. -/
theorem nodalCoefficientGroupIso_projection_of_eq
    (e : originalSmoothBaseChangeGroup S W ≅ CommGrp.mk (MultiplicativeGroupScheme.gm S))
    (he : e = (originalSmoothCoefficientGroupIso S W).symm ≪≫
      eqToIso (congrArg integralSmoothGroup h) ≪≫ integralSmoothSplitNodalTorusIso a) :
    e.inv.hom.hom.hom.left =
      (splitNodalRelativeSmoothOverIso a).hom.left ≫
        eqToHom (congrArg (fun V => (integralSmoothOpen V).toScheme) h.symm) ≫
          (originalSmoothCoefficientIso S W).hom := by
  rw [he, nodalCoefficientGroupIso_inv_left S W a h]

/-- A specified comparison also retains the full smooth-to-whole inclusion square. -/
@[reassoc] theorem nodalCoefficientGroupIso_inclusion_of_eq
    (e : originalSmoothBaseChangeGroup S W ≅ CommGrp.mk (MultiplicativeGroupScheme.gm S))
    (he : e = (originalSmoothCoefficientGroupIso S W).symm ≪≫
      eqToIso (congrArg integralSmoothGroup h) ≪≫ integralSmoothSplitNodalTorusIso a) :
    e.inv.hom.hom.hom.left ≫
      pullback.fst (integralSmoothStructure W)
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≫ (integralSmoothOpen W).ι =
      (splitNodalRelativeSmoothOverIso a).hom.left ≫
        (integralSmoothOpen (splitNodalEquation a)).ι ≫
          eqToHom (congrArg integralCurve h.symm) ≫ integralCoefficientMorphism (S := S) W := by
  rw [he, nodalCoefficientGroupIso_inv_inclusion S W a h]

end FLT.Mazur.OneGonSmoothing
