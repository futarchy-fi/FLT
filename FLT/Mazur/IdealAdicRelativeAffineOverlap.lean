/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeCoefficientSheafIso

/-!
# Coherent coefficient comparisons on arbitrary affine refinements

Every common affine refinement carries the normalized comparison of its
two ambient coefficient sheaves. These comparisons satisfy the cocycle
and commute with all further affine refinements.
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

/-- The normalized coefficient comparison on any common affine refinement. -/
def relativeCoefficientAffineOverlap {U V W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) :
    let := closedBaseAlgebra J f U.1
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f W.1
    (pullback (relativeTensorTransition J f i)).obj (relativeChartCoefficientSheaf J f U) ≅
      (pullback (relativeTensorTransition J f j)).obj (relativeChartCoefficientSheaf J f V) := by
  let := closedBaseAlgebra J f U.1
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f W.1
  exact relativeCoefficientPullbackIso J f i ≪≫ (relativeCoefficientPullbackIso J f j).symm

/-- The affine comparison retains both original coefficient restriction maps. -/
lemma relativeCoefficientAffineOverlap_hom_comp {U V W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) :
    let := closedBaseAlgebra J f U.1
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f W.1
    (relativeCoefficientAffineOverlap J f i j).hom ≫ relativeCoefficientSheafMap J f j =
      relativeCoefficientSheafMap J f i := by
  let := closedBaseAlgebra J f U.1
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f W.1
  change ((relativeCoefficientPullbackIso J f i).hom ≫
    (relativeCoefficientPullbackIso J f j).inv) ≫
      (relativeCoefficientPullbackIso J f j).hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, relativeCoefficientPullbackIso_hom]

/-- Comparing an affine chart with itself gives the identity. -/
lemma relativeCoefficientAffineOverlap_self {U W : X.affineOpens} (i : W.1 ⟶ U.1) :
    let := closedBaseAlgebra J f U.1
    let := closedBaseAlgebra J f W.1
    (relativeCoefficientAffineOverlap J f i i).hom = 𝟙 _ := by
  let := closedBaseAlgebra J f U.1
  let := closedBaseAlgebra J f W.1
  let _ := relativeCoefficientSheafMap_isIso J f i
  apply (cancel_mono (relativeCoefficientSheafMap J f i)).mp
  rw [relativeCoefficientAffineOverlap_hom_comp, Category.id_comp]

/-- Reversing the ambient affine charts inverts the comparison. -/
lemma relativeCoefficientAffineOverlap_symm {U V W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) :
    let := closedBaseAlgebra J f U.1
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f W.1
    (relativeCoefficientAffineOverlap J f i j).symm =
      relativeCoefficientAffineOverlap J f j i := by
  let := closedBaseAlgebra J f U.1
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f W.1
  apply Iso.ext
  rfl

/-- The cocycle holds on every common affine refinement. -/
lemma relativeCoefficientAffineOverlap_cocycle {U V T W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) (k : W.1 ⟶ T.1) :
    let := closedBaseAlgebra J f U.1
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f T.1
    let := closedBaseAlgebra J f W.1
    (relativeCoefficientAffineOverlap J f i j).hom ≫
        (relativeCoefficientAffineOverlap J f j k).hom =
      (relativeCoefficientAffineOverlap J f i k).hom := by
  let := closedBaseAlgebra J f U.1
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f T.1
  let := closedBaseAlgebra J f W.1
  let _ := relativeCoefficientSheafMap_isIso J f k
  apply (cancel_mono (relativeCoefficientSheafMap J f k)).mp
  rw [Category.assoc, relativeCoefficientAffineOverlap_hom_comp,
    relativeCoefficientAffineOverlap_hom_comp, relativeCoefficientAffineOverlap_hom_comp]

/-- The normalized affine comparisons commute with every further affine refinement. -/
lemma relativeCoefficientAffineOverlap_refine {U V W Z : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) (k : Z.1 ⟶ W.1) :
    let := closedBaseAlgebra J f U.1
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f W.1
    let := closedBaseAlgebra J f Z.1
    (pullback (relativeTensorTransition J f k)).map
          (relativeCoefficientAffineOverlap J f i j).hom ≫
        (relativeCoefficientCompositeIso J f k j).hom =
      (relativeCoefficientCompositeIso J f k i).hom ≫
        (relativeCoefficientAffineOverlap J f (k ≫ i) (k ≫ j)).hom := by
  let := closedBaseAlgebra J f U.1
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f W.1
  let := closedBaseAlgebra J f Z.1
  let _ := relativeCoefficientSheafMap_isIso J f (k ≫ j)
  apply (cancel_mono (relativeCoefficientSheafMap J f (k ≫ j))).mp
  rw [Category.assoc, Category.assoc,
    relativeCoefficientAffineOverlap_hom_comp,
    ← relativeCoefficientSheafMap_comp_forward J f k j,
    ← relativeCoefficientSheafMap_comp_forward J f k i,
    ← Category.assoc, ← Functor.map_comp, relativeCoefficientAffineOverlap_hom_comp]

/-- The affine comparison extends the previously constructed principal comparison. -/
lemma relativeCoefficientAffineOverlap_eq_principal {U V W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) (r : Γ(X, U.1)) (s : Γ(X, V.1))
    (hr : W.1 = X.basicOpen r) (hs : W.1 = X.basicOpen s) :
    let := closedBaseAlgebra J f U.1
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f W.1
    relativeCoefficientAffineOverlap J f i j =
      relativeCoefficientPrincipalOverlap J f i j r s hr hs := by
  let := closedBaseAlgebra J f U.1
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f W.1
  let _ := relativeCoefficientSheafMap_isIso J f j
  apply Iso.ext
  apply (cancel_mono (relativeCoefficientSheafMap J f j)).mp
  rw [relativeCoefficientAffineOverlap_hom_comp, relativeCoefficientPrincipalOverlap_hom_comp]

end FLT.Mazur.IdealAdicGradedPullback
