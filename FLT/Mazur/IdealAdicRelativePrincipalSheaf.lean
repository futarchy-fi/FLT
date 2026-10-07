/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeCoefficientBaseChange
public import FLT.Mazur.AffineModulePullbackSections

/-!
# The actual coefficient sheaves on principal chart refinements

The sheaf on a principal refinement is canonically the pullback, and hence
the open restriction, of the original chart coefficient sheaf. The comparison
uses the original coefficient scalar-extension isomorphism.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

attribute [local irreducible] relativeRestriction relativeMap

/-- Pullback along the actual principal transition recovers the original refined sheaf. -/
def relativeCoefficientPrincipalPullbackIso (V : X.affineOpens) (r : Γ(X, V.1)) :
    let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
    let i : U.1 ⟶ V.1 := homOfLE (X.basicOpen_le r)
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f U.1
    (pullback (relativeTensorTransition J f i)).obj (relativeChartCoefficientSheaf J f V) ≅
      relativeChartCoefficientSheaf J f U := by
  let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
  let i : U.1 ⟶ V.1 := homOfLE (X.basicOpen_le r)
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f U.1
  exact ((AffineModulePullbackSections.tildePullbackIso
    (CommRingCat.ofHom (relativeRestriction J f i).toRingHom)).app
      (relativeChartCoefficient J f V)).symm ≪≫
    (tilde.functor (.of (RelativeAlgebra J f U))).mapIso (relativeCoefficientBaseChange J f V r)

/-- The actual chart coefficient sheaf restricts isomorphically to the principal refined sheaf. -/
def relativeCoefficientPrincipalRestrictIso (V : X.affineOpens) (r : Γ(X, V.1)) :
    let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
    let i : U.1 ⟶ V.1 := homOfLE (X.basicOpen_le r)
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f U.1
    let _ := relativeTensorTransition_isOpenImmersion J f i
    (relativeChartCoefficientSheaf J f V).restrict (relativeTensorTransition J f i) ≅
      relativeChartCoefficientSheaf J f U := by
  let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
  let i : U.1 ⟶ V.1 := homOfLE (X.basicOpen_le r)
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f U.1
  let _ := relativeTensorTransition_isOpenImmersion J f i
  exact (restrictFunctorIsoPullback (relativeTensorTransition J f i)).app
    (relativeChartCoefficientSheaf J f V) ≪≫ relativeCoefficientPrincipalPullbackIso J f V r

end FLT.Mazur.IdealAdicGradedPullback
