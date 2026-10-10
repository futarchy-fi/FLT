/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativePrincipalSections
public import FLT.Mazur.AffineTildeSemilinearMap

/-!
# Actual coefficient sheaf maps for all affine inclusions

Original coefficient restrictions induce normalized sheaf maps along every
relative tensor transition. On principal inclusions these are the proved
isomorphisms, rather than separately chosen transition maps.
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

/-- The original coefficient restriction induces a map of the actual relative chart sheaves. -/
def relativeCoefficientSheafMap {U V : X.affineOpens} (i : U.1 ⟶ V.1) :
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f U.1
    (pullback (relativeTensorTransition J f i)).obj (relativeChartCoefficientSheaf J f V) ⟶
      relativeChartCoefficientSheaf J f U := by
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f U.1
  exact AffineTildeSemilinearMap.map
    (CommRingCat.ofHom (relativeRestriction J f i).toRingHom)
    (relativeChartCoefficient J f V) (relativeChartCoefficient J f U)
    (ModuleCat.ofHom (X := relativeChartCoefficient J f V)
      (Y := relativeRestrictedCoefficient J f i) (relativeCoefficientRestrictionLinear J f i))

/-- The sheaf map uses the original restriction on every original section. -/
lemma relativeCoefficientSheafMap_unit {U V : X.affineOpens} (i : U.1 ⟶ V.1) :
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f U.1
    ∀ s : relativeChartCoefficient J f V,
      (moduleSpecΓFunctor (R := .of (RelativeAlgebra J f U))).map
          (relativeCoefficientSheafMap J f i)
          (AffineTildePullbackSectionMap.unit
            (CommRingCat.ofHom (relativeRestriction J f i).toRingHom)
            (relativeChartCoefficient J f V) s) =
        (relativeChartCoefficientSectionsIso J f U).hom
          (restrictRingHom (J.comap f) U.1 i s) := by
  intro _ _ s
  exact AffineTildePullbackSectionMap.semilinearMap_unit
    (CommRingCat.ofHom (relativeRestriction J f i).toRingHom)
    (relativeChartCoefficient J f V) (relativeChartCoefficient J f U)
    (ModuleCat.ofHom (X := relativeChartCoefficient J f V)
      (Y := relativeRestrictedCoefficient J f i) (relativeCoefficientRestrictionLinear J f i)) s

/-- On principal refinements the map is the already constructed principal sheaf comparison. -/
lemma relativeCoefficientSheafMap_principal (V : X.affineOpens) (r : Γ(X, V.1)) :
    let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
    let i : U.1 ⟶ V.1 := homOfLE (X.basicOpen_le r)
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f U.1
    relativeCoefficientSheafMap J f i =
      (relativeCoefficientPrincipalPullbackIso J f V r).hom := by
  intro U i _ _
  apply AffineTildePullbackSectionMap.hom_ext
    (CommRingCat.ofHom (relativeRestriction J f i).toRingHom)
    (relativeChartCoefficient J f V)
  intro s
  exact (relativeCoefficientSheafMap_unit J f i s).trans
    (relativeCoefficientPrincipalPullbackIso_unit J f V r s).symm

/-- The normalized sheaf map is invertible on each principal refinement. -/
lemma relativeCoefficientSheafMap_principal_isIso (V : X.affineOpens) (r : Γ(X, V.1)) :
    let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
    let i : U.1 ⟶ V.1 := homOfLE (X.basicOpen_le r)
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f U.1
    IsIso (relativeCoefficientSheafMap J f i) := by
  intro U i _ _
  rw [relativeCoefficientSheafMap_principal]
  infer_instance

end FLT.Mazur.IdealAdicGradedPullback
