/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeCoefficientModuleMap
public import FLT.Mazur.AffineTildeMorphismCoherence

/-!
# Refinement compatibility of the actual coefficient sheaf maps

The original restrictions give the sheaf-level composition law, with the
canonical geometric pullback comparison. Principal comparisons therefore
commute on further refinements.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.IdealAdicGradedSections

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

attribute [local irreducible] relativeRestriction relativeMap
attribute [local irreducible] Scheme.Modules.pullback
attribute [local irreducible] AffineIteratedPullbackSections.compositeIso
attribute [local irreducible] relativeCoefficientSheafMap

/-- The actual geometric identification between the iterated and composite chart pullbacks. -/
def relativeCoefficientCompositeIso {U V W : X.affineOpens}
    (i : U.1 ⟶ V.1) (j : V.1 ⟶ W.1) :
    let := closedBaseAlgebra J f U.1
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f W.1
    (pullback (relativeTensorTransition J f i)).obj
        ((pullback (relativeTensorTransition J f j)).obj
          (relativeChartCoefficientSheaf J f W)) ≅
      (pullback (relativeTensorTransition J f (i ≫ j))).obj
        (relativeChartCoefficientSheaf J f W) := by
  let := closedBaseAlgebra J f U.1
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f W.1
  exact AffineIteratedPullbackSections.compositeIso
    (relativeTensorTransition J f i) (relativeTensorTransition J f j)
    (relativeTensorTransition J f (i ≫ j)) (relativeTensorTransition_comp J f i j)
    (relativeChartCoefficientSheaf J f W)

/-- The geometric comparison has the literal affine-comparison expression. -/
lemma relativeCoefficientCompositeIso_eq {U V W : X.affineOpens}
    (i : U.1 ⟶ V.1) (j : V.1 ⟶ W.1) :
    let := closedBaseAlgebra J f U.1
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f W.1
    relativeCoefficientCompositeIso J f i j = AffineIteratedPullbackSections.compositeIso
      (Spec.map (CommRingCat.ofHom (relativeRestriction J f i).toRingHom))
      (Spec.map (CommRingCat.ofHom (relativeRestriction J f j).toRingHom))
      (Spec.map (CommRingCat.ofHom (relativeRestriction J f (i ≫ j)).toRingHom))
      (relativeTensorTransition_comp J f i j) (tilde (relativeChartCoefficient J f W)) := rfl

/-- Normalize the actual map using the bundled coefficient morphism on original sections. -/
lemma relativeCoefficientSheafMap_unit_moduleMap {U V : X.affineOpens} (i : U.1 ⟶ V.1) :
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f U.1
    ∀ m : relativeChartCoefficient J f V,
      (moduleSpecΓFunctor (R := .of (RelativeAlgebra J f U))).map
          (relativeCoefficientSheafMap J f i)
          (AffineTildePullbackSectionMap.unit
            (CommRingCat.ofHom (relativeRestriction J f i).toRingHom)
            (relativeChartCoefficient J f V) m) =
        (tilde.toTildeΓNatIso (R := .of (RelativeAlgebra J f U))).hom.app
          (relativeChartCoefficient J f U) (relativeCoefficientModuleMap J f i m) := by
  intro _ _ m
  exact relativeCoefficientSheafMap_unit J f i m

/-- Original coefficient sheaf maps satisfy composition along every pair of refinements. -/
lemma relativeCoefficientSheafMap_comp {U V W : X.affineOpens}
    (i : U.1 ⟶ V.1) (j : V.1 ⟶ W.1) :
    let := closedBaseAlgebra J f U.1
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f W.1
    (relativeCoefficientCompositeIso J f i j).inv ≫
        (pullback (relativeTensorTransition J f i)).map (relativeCoefficientSheafMap J f j) ≫
        relativeCoefficientSheafMap J f i = relativeCoefficientSheafMap J f (i ≫ j) := by
  let := closedBaseAlgebra J f U.1
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f W.1
  rw [relativeCoefficientCompositeIso_eq J f i j]
  exact AffineTildeMorphismCoherence.hom_comp
    (CommRingCat.ofHom (relativeRestriction J f j).toRingHom)
    (CommRingCat.ofHom (relativeRestriction J f i).toRingHom)
    (CommRingCat.ofHom (relativeRestriction J f (i ≫ j)).toRingHom)
    (relativeTensorTransition_comp J f i j)
    (relativeChartCoefficient J f W) (relativeChartCoefficient J f V)
    (relativeChartCoefficient J f U)
    (relativeCoefficientSheafMap J f j) (relativeCoefficientSheafMap J f i)
    (relativeCoefficientSheafMap J f (i ≫ j))
    (relativeCoefficientModuleMap J f j) (relativeCoefficientModuleMap J f i)
    (relativeCoefficientModuleMap J f (i ≫ j))
    (relativeCoefficientSheafMap_unit_moduleMap J f j)
    (relativeCoefficientSheafMap_unit_moduleMap J f i)
    (relativeCoefficientSheafMap_unit_moduleMap J f (i ≫ j))
    (relativeCoefficientModuleMap_comp J f i j)

end FLT.Mazur.IdealAdicGradedPullback
