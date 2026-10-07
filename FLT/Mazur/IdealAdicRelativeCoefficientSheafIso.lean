/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativePrincipalOverlapRefinement
public import FLT.Mazur.IdealAdicRelativeTransitionRefinement
public import FLT.Mazur.ModuleSheafPullbackIsoDetection

/-!
# Invertibility of all original affine coefficient sheaf maps

Common principal refinements cover each transition source. On each of
these refinements the actual map is invertible by composition and the
principal comparison, so open-immersion pullbacks detect its invertibility.
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

attribute [local irreducible] relativeRestriction relativeMap relativeCoefficientSheafMap

attribute [local irreducible] relativeCoefficientCompositeIso Scheme.Modules.pullback

/-- The original coefficient sheaf map is invertible for every affine inclusion. -/
lemma relativeCoefficientSheafMap_isIso {U V : X.affineOpens} (i : U.1 ⟶ V.1) :
    let := closedBaseAlgebra J f U.1
    let := closedBaseAlgebra J f V.1
    IsIso (relativeCoefficientSheafMap J f i) := by
  let := closedBaseAlgebra J f U.1
  let := closedBaseAlgebra J f V.1
  let C := {rs : Γ(X, U.1) × Γ(X, V.1) // X.basicOpen rs.1 = X.basicOpen rs.2}
  let W (c : C) : X.affineOpens := ⟨X.basicOpen c.val.1, U.2.basicOpen c.val.1⟩
  let g (c : C) : (W c).1 ⟶ U.1 := homOfLE (X.basicOpen_le c.val.1)
  let Z (c : C) : Scheme := (relativeTensorDiagram J f).obj (W c)
  let k (c : C) : Z c ⟶ Spec (.of (RelativeAlgebra J f U)) :=
    relativeTensorTransition J f (g c)
  let _ (c : C) : IsOpenImmersion (k c) :=
    relativeTensorTransition_isOpenImmersion J f (g c)
  apply ModuleSheafPullbackIsoDetection.isIso_of_openImmersionPullbacks
    (relativeCoefficientSheafMap J f i) Z k
  · intro x
    obtain ⟨r, s, hrs, hx⟩ := relativeTensorTransition_exists_common_principal J f i x
    exact ⟨⟨(r, s), hrs⟩, hx⟩
  · intro c
    exact relativeCoefficientSheafMap_pullback_isIso J f (g c) i
      c.val.1 c.val.2 rfl c.property

/-- Every original affine coefficient restriction gives an actual pullback isomorphism. -/
def relativeCoefficientPullbackIso {U V : X.affineOpens} (i : U.1 ⟶ V.1) :
    let := closedBaseAlgebra J f U.1
    let := closedBaseAlgebra J f V.1
    (pullback (relativeTensorTransition J f i)).obj (relativeChartCoefficientSheaf J f V) ≅
      relativeChartCoefficientSheaf J f U := by
  let := closedBaseAlgebra J f U.1
  let := closedBaseAlgebra J f V.1
  let _ := relativeCoefficientSheafMap_isIso J f i
  exact asIso (relativeCoefficientSheafMap J f i)

/-- The isomorphism retains the actual coefficient restriction morphism. -/
lemma relativeCoefficientPullbackIso_hom {U V : X.affineOpens} (i : U.1 ⟶ V.1) :
    let := closedBaseAlgebra J f U.1
    let := closedBaseAlgebra J f V.1
    (relativeCoefficientPullbackIso J f i).hom = relativeCoefficientSheafMap J f i := rfl

end FLT.Mazur.IdealAdicGradedPullback
