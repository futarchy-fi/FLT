/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothCoefficientProjection
public import FLT.Mazur.WeierstrassSmoothCoefficientGroupIso
public import FLT.Mazur.WeierstrassSmoothGroupEquationTransport

/-!
# The one-gon coefficient projection preserves its intrinsic smooth group

Equation transport identifies the geometric smooth coefficient comparison
with the existing group comparison, even along a singular coefficient fiber.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.OneGonSmoothing

open WeierstrassIntegralChart WeierstrassDividedDepth

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (t : R)

/-- The actual intrinsic smooth group is the coefficient base change group. -/
irreducible_def smoothCoefficientGroupIso :
    integralSmoothGroup (equation (algebraMap R S t)) ≅
      originalSmoothBaseChangeGroup S (equation t) :=
  smoothEquationGroupIso (equation_map t (algebraMap R S)).symm ≪≫
    originalSmoothCoefficientGroupIso S (equation t)

/-- The group comparison retains the transported geometric smooth isomorphism. -/
theorem smoothCoefficientGroupIso_hom :
    (smoothCoefficientGroupIso (S := S) t).hom.hom.hom.hom.left =
      eqToHom (congrArg (fun W => (integralSmoothOpen W).toScheme)
        (equation_map t (algebraMap R S)).symm) ≫
          (originalSmoothCoefficientIso S (equation t)).hom := by
  rw [smoothCoefficientGroupIso_def]
  exact congrArg₂ (fun a b => a ≫ b)
    (smoothEquationGroupIso_hom_left (equation_map t (algebraMap R S)).symm)
    (originalSmoothCoefficientGroupIso_hom S (equation t))

/-- Its geometric first projection is exactly the original smooth coefficient map. -/
@[reassoc] theorem smoothCoefficientGroupIso_fst :
    (smoothCoefficientGroupIso (S := S) t).hom.hom.hom.hom.left ≫
      pullback.fst (integralSmoothStructure (equation t))
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
          smoothCoefficientProjection (S := S) t := by
  rw [smoothCoefficientGroupIso_hom, Category.assoc, originalSmoothCoefficientIso_fst]
  rfl

/-- Forgetting the bundled group comparison gives its actual relative scheme isomorphism. -/
def smoothCoefficientGroupOverIso :
    (integralSmoothGroup (equation (algebraMap R S t))).X ≅
      (originalSmoothBaseChangeGroup S (equation t)).X :=
  (CommGrp.forget (Over (Spec (.of S)))).mapIso
    (smoothCoefficientGroupIso t)

instance smoothCoefficientGroupOverIso_isMonHom :
    IsMonHom (smoothCoefficientGroupOverIso (S := S) t).hom := by
  change IsMonHom (smoothCoefficientGroupIso (S := S) t).hom.hom.hom.hom
  infer_instance

end FLT.Mazur.OneGonSmoothing
