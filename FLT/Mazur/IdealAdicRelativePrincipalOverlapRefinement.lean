/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativePrincipalOverlap
public import FLT.Mazur.IdealAdicRelativeCoefficientSheafCoherence

/-!
# Compatibility of principal overlap comparisons under refinement

The actual coefficient restrictions commute with the geometric composition
comparison. Consequently normalized overlap isomorphisms agree after any
further refinement that is principal in both ambient charts.
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

/-- Forward form of composition, retaining the geometric pullback comparison. -/
lemma relativeCoefficientSheafMap_comp_forward {U V W : X.affineOpens}
    (i : U.1 ⟶ V.1) (j : V.1 ⟶ W.1) :
    let := closedBaseAlgebra J f U.1
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f W.1
    (pullback (relativeTensorTransition J f i)).map (relativeCoefficientSheafMap J f j) ≫
        relativeCoefficientSheafMap J f i =
      (relativeCoefficientCompositeIso J f i j).hom ≫
        relativeCoefficientSheafMap J f (i ≫ j) := by
  let := closedBaseAlgebra J f U.1
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f W.1
  rw [← relativeCoefficientSheafMap_comp J f i j, Iso.hom_inv_id_assoc]

/-- On a common principal refinement the pullback of any inclusion map is invertible. -/
lemma relativeCoefficientSheafMap_pullback_isIso {U V W : X.affineOpens}
    (i : U.1 ⟶ V.1) (j : V.1 ⟶ W.1) (r : Γ(X, V.1)) (s : Γ(X, W.1))
    (hr : U.1 = X.basicOpen r) (hs : U.1 = X.basicOpen s) :
    let := closedBaseAlgebra J f U.1
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f W.1
    IsIso ((pullback (relativeTensorTransition J f i)).map
      (relativeCoefficientSheafMap J f j)) := by
  let := closedBaseAlgebra J f U.1
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f W.1
  let _ := relativeCoefficientSheafMap_isIso_of_basicOpen J f i r hr
  let _ := relativeCoefficientSheafMap_isIso_of_basicOpen J f (i ≫ j) s hs
  have : IsIso ((pullback (relativeTensorTransition J f i)).map
      (relativeCoefficientSheafMap J f j) ≫ relativeCoefficientSheafMap J f i) := by
    rw [relativeCoefficientSheafMap_comp_forward J f i j]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (relativeCoefficientSheafMap J f i)

/-- Common-principal comparisons commute with further common-principal refinement. -/
lemma relativeCoefficientPrincipalOverlap_refine {U V W Z : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) (k : Z.1 ⟶ W.1)
    (r : Γ(X, U.1)) (s : Γ(X, V.1)) (r' : Γ(X, U.1)) (s' : Γ(X, V.1))
    (hr : W.1 = X.basicOpen r) (hs : W.1 = X.basicOpen s)
    (hr' : Z.1 = X.basicOpen r') (hs' : Z.1 = X.basicOpen s') :
    let := closedBaseAlgebra J f U.1
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f W.1
    let := closedBaseAlgebra J f Z.1
    (pullback (relativeTensorTransition J f k)).map
          (relativeCoefficientPrincipalOverlap J f i j r s hr hs).hom ≫
        (relativeCoefficientCompositeIso J f k j).hom =
      (relativeCoefficientCompositeIso J f k i).hom ≫
        (relativeCoefficientPrincipalOverlap J f (k ≫ i) (k ≫ j) r' s' hr' hs').hom := by
  let := closedBaseAlgebra J f U.1
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f W.1
  let := closedBaseAlgebra J f Z.1
  let _ := relativeCoefficientSheafMap_isIso_of_basicOpen J f (k ≫ j) s' hs'
  apply (cancel_mono (relativeCoefficientSheafMap J f (k ≫ j))).mp
  rw [Category.assoc, Category.assoc,
    relativeCoefficientPrincipalOverlap_hom_comp J f (k ≫ i) (k ≫ j) r' s' hr' hs',
    ← relativeCoefficientSheafMap_comp_forward J f k j,
    ← relativeCoefficientSheafMap_comp_forward J f k i,
    ← Category.assoc, ← Functor.map_comp,
    relativeCoefficientPrincipalOverlap_hom_comp J f i j r s hr hs]

end FLT.Mazur.IdealAdicGradedPullback
