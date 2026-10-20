/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonNodalCoefficient
public import FLT.Mazur.RootsOfUnityGroupBaseChange

/-!
# The arithmetic boundary torus commutes with actual base change

The corrected original pinching coordinate on the zero-parameter cubic agrees
with the coordinate on its categorical coefficient pullback.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj GrpObj

open scoped CategoryTheory.Obj

namespace FLT.Mazur.ArithmeticOneGonTorusBaseChange

open OneGonSmoothing WeierstrassIntegralChart
open RootsOfUnityInclusionBaseChange CharacterSchemeBaseChange

variable (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
local notation "q" => baseMap R A
local notation "e" => ArithmeticOneGonFiberTorus.groupIso A (0 : R) (map_zero _)

/-- The uncorrected nodal parametrization is the actual coefficient pullback. -/
theorem nodal_comparison :
    (torusComparison R A).hom ≫
        (Over.pullback q).map (splitNodalRelativeSmoothOverIso (-1 : Rˣ)).hom =
      (e).inv.hom.hom.hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · apply (cancel_mono (integralSmoothOpen (equation (0 : R))).ι).mp
    simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst]
    rw [← Category.assoc, torusComparison_fst]
    erw [nodalCoefficientGroupIso_inclusion_of_eq A (equation (0 : R)) (-1 : Aˣ)
      (ArithmeticOneGonFiberTorus.equation_zero A (0 : R) (map_zero _)) (e)
      (ArithmeticOneGonFiberTorus.groupIso_def A (0 : R) (map_zero _))]
    change Spec.map (CommRingCat.ofHom
        (CharacterAlgebraScalarExtension.coeff R A ℤ).toRingHom) ≫
          splitNodalTorusToSmooth (-1 : Rˣ) ≫ (integralSmoothOpen _).ι =
      splitNodalTorusToSmooth (-1 : Aˣ) ≫ (integralSmoothOpen _).ι ≫ _ ≫ _
    rw [splitNodalTorusToSmooth_inclusion, splitNodalTorusToSmooth_inclusion_assoc]
    exact ArithmeticOneGonNodalCoefficient.torus_coefficient R A
  · exact (Over.w _).trans (Over.w _).symm

/-- Coefficient pullback preserves inversion on the actual torus group. -/
theorem inversion_comparison :
    (torusComparison R A).hom ≫ (Over.pullback q).map ι[MultiplicativeGroupScheme.gm R] =
      ι[MultiplicativeGroupScheme.gm A] ≫ (torusComparison R A).hom :=
  (GrpObj.inv_hom (torusComparison R A).hom).symm

/-- The arithmetic torus and the fiber torus use precisely the same corrected coordinate. -/
theorem torus_comparison :
    (torusComparison R A).hom ≫ (Over.pullback q).map (ArithmeticOneGonTorus.torusIso R).hom =
      (ArithmeticOneGonFiberTorus.torusIso A (0 : R) (map_zero _)).hom := by
  rw [ArithmeticOneGonTorus.torusIso_hom, Functor.map_comp,
    ← Category.assoc, inversion_comparison, Category.assoc, nodal_comparison]
  rfl

end FLT.Mazur.ArithmeticOneGonTorusBaseChange
