/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeCoefficientSheafMap
public import FLT.Mazur.IdealAdicRelativeCommonRefinement

/-!
# Coefficient comparisons on common principal charts

An affine chart which is principal in two ambient charts identifies their
pulled-back coefficient sheaves through its original coefficient sheaf.
The comparison retains both original restriction maps.
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

/-- Principal invertibility is independent of the chosen presentation of the smaller chart. -/
lemma relativeCoefficientSheafMap_isIso_of_basicOpen {U V : X.affineOpens}
    (i : U.1 ⟶ V.1) (r : Γ(X, V.1)) (h : U.1 = X.basicOpen r) :
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f U.1
    IsIso (relativeCoefficientSheafMap J f i) := by
  have he : U = ⟨X.basicOpen r, V.2.basicOpen r⟩ := Subtype.ext h
  subst U
  have hi : i = homOfLE (X.basicOpen_le r) := Subsingleton.elim _ _
  subst i
  exact relativeCoefficientSheafMap_principal_isIso J f V r

/-- The two chart sheaves agree on any specified common principal refinement. -/
def relativeCoefficientPrincipalOverlap {U V W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1)
    (r : Γ(X, U.1)) (s : Γ(X, V.1))
    (hr : W.1 = X.basicOpen r) (hs : W.1 = X.basicOpen s) :
    let := closedBaseAlgebra J f U.1
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f W.1
    (pullback (relativeTensorTransition J f i)).obj (relativeChartCoefficientSheaf J f U) ≅
      (pullback (relativeTensorTransition J f j)).obj (relativeChartCoefficientSheaf J f V) := by
  let := closedBaseAlgebra J f U.1
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f W.1
  let _ := relativeCoefficientSheafMap_isIso_of_basicOpen J f i r hr
  let _ := relativeCoefficientSheafMap_isIso_of_basicOpen J f j s hs
  exact asIso (relativeCoefficientSheafMap J f i) ≪≫
    (asIso (relativeCoefficientSheafMap J f j)).symm

/-- The overlap comparison is normalized by the two original coefficient restriction maps. -/
lemma relativeCoefficientPrincipalOverlap_hom_comp {U V W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1)
    (r : Γ(X, U.1)) (s : Γ(X, V.1))
    (hr : W.1 = X.basicOpen r) (hs : W.1 = X.basicOpen s) :
    let := closedBaseAlgebra J f U.1
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f W.1
    (relativeCoefficientPrincipalOverlap J f i j r s hr hs).hom ≫
      relativeCoefficientSheafMap J f j = relativeCoefficientSheafMap J f i := by
  let := closedBaseAlgebra J f U.1
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f W.1
  let _ := relativeCoefficientSheafMap_isIso_of_basicOpen J f j s hs
  change (relativeCoefficientSheafMap J f i ≫ inv (relativeCoefficientSheafMap J f j)) ≫
    relativeCoefficientSheafMap J f j = _
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

end FLT.Mazur.IdealAdicGradedPullback
