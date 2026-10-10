/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeCoefficientSheafMap

/-!
# Bundled original coefficient maps

The original semilinear restriction defines a module morphism. This stable
interface connects sheaf maps and coefficient composition without unfolding
the construction of the coefficient modules in later coherence proofs.
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
attribute [local irreducible] AffineTildeSemilinearMap.map

/-- The original restriction, bundled as a morphism with restricted target scalars. -/
def relativeCoefficientModuleMap {U V : X.affineOpens} (i : U.1 ⟶ V.1) :
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f U.1
    relativeChartCoefficient J f V ⟶
      (ModuleCat.restrictScalars (relativeRestriction J f i).toRingHom).obj
        (relativeChartCoefficient J f U) := by
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f U.1
  exact ModuleCat.ofHom (X := relativeChartCoefficient J f V)
    (Y := relativeRestrictedCoefficient J f i) (relativeCoefficientRestrictionLinear J f i)

/-- The bundled morphism acts by the original semilinear restriction. -/
lemma relativeCoefficientModuleMap_apply {U V : X.affineOpens} (i : U.1 ⟶ V.1)
    (s : IdealAdicGradedSections.Sections (J.comap f) V.1) :
    relativeCoefficientModuleMap J f i s = relativeCoefficientRestriction J f i s := rfl

/-- Composition of bundled morphisms is composition of the original coefficient restrictions. -/
lemma relativeCoefficientModuleMap_comp {U V W : X.affineOpens}
    (i : U.1 ⟶ V.1) (j : V.1 ⟶ W.1) (s : relativeChartCoefficient J f W) :
    relativeCoefficientModuleMap J f i (relativeCoefficientModuleMap J f j s) =
      relativeCoefficientModuleMap J f (i ≫ j) s := by
  simp only [relativeCoefficientModuleMap_apply]
  exact relativeCoefficientRestriction_comp J f i j s

/-- The actual sheaf map is the normalized map of the bundled original restriction. -/
lemma relativeCoefficientSheafMap_eq_moduleMap {U V : X.affineOpens} (i : U.1 ⟶ V.1) :
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f U.1
    relativeCoefficientSheafMap J f i = AffineTildeSemilinearMap.map
      (CommRingCat.ofHom (relativeRestriction J f i).toRingHom)
      (relativeChartCoefficient J f V) (relativeChartCoefficient J f U)
      (relativeCoefficientModuleMap J f i) := rfl

end FLT.Mazur.IdealAdicGradedPullback
