/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativePrincipalOverlap

/-!
# Cocycle on a fixed common principal chart

On a chart principal in all participating ambient charts, the normalized
coefficient comparisons satisfy identity, symmetry, and composition. These
laws do not yet assert compatibility between different refinement charts.
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

/-- A comparison from a chart to itself on a common principal chart is the identity. -/
lemma relativeCoefficientPrincipalOverlap_self {U W : X.affineOpens}
    (i : W.1 ⟶ U.1) (r : Γ(X, U.1)) (hr : W.1 = X.basicOpen r) :
    let := closedBaseAlgebra J f U.1
    let := closedBaseAlgebra J f W.1
    (relativeCoefficientPrincipalOverlap J f i i r r hr hr).hom = 𝟙 _ := by
  let := closedBaseAlgebra J f U.1
  let := closedBaseAlgebra J f W.1
  let _ := relativeCoefficientSheafMap_isIso_of_basicOpen J f i r hr
  apply (cancel_mono (relativeCoefficientSheafMap J f i)).mp
  rw [relativeCoefficientPrincipalOverlap_hom_comp J f i i r r hr hr, Category.id_comp]

/-- Exchanging the two ambient charts inverts their common-principal comparison. -/
lemma relativeCoefficientPrincipalOverlap_symm {U V W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1)
    (r : Γ(X, U.1)) (s : Γ(X, V.1))
    (hr : W.1 = X.basicOpen r) (hs : W.1 = X.basicOpen s) :
    let := closedBaseAlgebra J f U.1
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f W.1
    (relativeCoefficientPrincipalOverlap J f i j r s hr hs).symm =
      relativeCoefficientPrincipalOverlap J f j i s r hs hr := by
  let := closedBaseAlgebra J f U.1
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f W.1
  apply Iso.ext
  rfl

/-- The original coefficient comparisons satisfy the cocycle on a fixed common principal chart. -/
lemma relativeCoefficientPrincipalOverlap_cocycle {U V T W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) (k : W.1 ⟶ T.1)
    (r : Γ(X, U.1)) (s : Γ(X, V.1)) (t : Γ(X, T.1))
    (hr : W.1 = X.basicOpen r) (hs : W.1 = X.basicOpen s)
    (ht : W.1 = X.basicOpen t) :
    let := closedBaseAlgebra J f U.1
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f T.1
    let := closedBaseAlgebra J f W.1
    (relativeCoefficientPrincipalOverlap J f i j r s hr hs).hom ≫
        (relativeCoefficientPrincipalOverlap J f j k s t hs ht).hom =
      (relativeCoefficientPrincipalOverlap J f i k r t hr ht).hom := by
  let := closedBaseAlgebra J f U.1
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f T.1
  let := closedBaseAlgebra J f W.1
  let _ := relativeCoefficientSheafMap_isIso_of_basicOpen J f k t ht
  apply (cancel_mono (relativeCoefficientSheafMap J f k)).mp
  rw [Category.assoc, relativeCoefficientPrincipalOverlap_hom_comp J f j k s t hs ht,
    relativeCoefficientPrincipalOverlap_hom_comp J f i j r s hr hs,
    relativeCoefficientPrincipalOverlap_hom_comp J f i k r t hr ht]

end FLT.Mazur.IdealAdicGradedPullback
