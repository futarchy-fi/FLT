/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeTransitionGeometry
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Principal localization of the original relative tensor rings

Closed principal refinements localize the original tensor restriction at the
right tensor inclusion. Ambient principal opens give such refinements.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.IdealAdicGradedSections
open scoped TensorProduct

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

omit [IsLocallyNoetherian Y] in
/-- A principal refinement of the actual closed chart localizes its original restriction. -/
lemma closedRestriction_isLocalization {U V : X.affineOpens} (i : U.1 ⟶ V.1)
    (r : ClosedScalars (J.comap f) V.1)
    (h : (closedAffineChart J f U).1 = (J.comap f).subscheme.basicOpen r) :
    let := (closedScalarRestriction (J.comap f) i).toAlgebra
    IsLocalization.Away r (ClosedScalars (J.comap f) U.1) :=
  (closedAffineChart J f V).2.isLocalization_of_eq_basicOpen r _ h

/-- The original relative tensor map is localization at the right inclusion of a scalar. -/
lemma relativeRestriction_isLocalization {U V : X.affineOpens} (i : U.1 ⟶ V.1)
    (r : ClosedScalars (J.comap f) V.1)
    (h : (closedAffineChart J f U).1 = (J.comap f).subscheme.basicOpen r) :
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f U.1
    let := (relativeRestriction J f i).toAlgebra
    IsLocalization.Away ((1 : IdealAdicGradedSections.Sections J ⊤) ⊗ₜ[Γ(Y, ⊤)] r)
      (RelativeAlgebra J f U) := by
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f U.1
  let := (closedScalarRestriction (J.comap f) i).toAlgebra
  let := (relativeRestriction J f i).toAlgebra
  let _ : IsScalarTower Γ(Y, ⊤) (ClosedScalars (J.comap f) V.1)
      (ClosedScalars (J.comap f) U.1) :=
    IsScalarTower.of_algebraMap_eq (fun r ↦ (closedBaseMap_restrict J f i r).symm)
  let _ : IsScalarTower (IdealAdicGradedSections.Sections J ⊤) (RelativeAlgebra J f V)
      (RelativeAlgebra J f U) :=
    IsScalarTower.of_algebraMap_eq (fun r ↦ ((relativeRestriction J f i).commutes r).symm)
  let _ := closedRestriction_isLocalization J f i r h
  have H := IsLocalization.tensorProduct_tensorProduct_right Γ(Y, ⊤)
    (IdealAdicGradedSections.Sections J ⊤)
    (.powers r) (ClosedScalars (J.comap f) U.1) (by
      ext s
      exact relativeRestriction_tmul J f i 1 s)
  simpa only [Submonoid.map_powers, Algebra.TensorProduct.includeRight_apply] using H

omit [IsLocallyNoetherian Y] in
/-- An ambient principal refinement is a principal refinement of the actual closed chart. -/
lemma closedAffineChart_basicOpen (V : X.affineOpens) (r : Γ(X, V.1)) :
    (closedAffineChart J f ⟨X.basicOpen r, V.2.basicOpen r⟩).1 =
      (J.comap f).subscheme.basicOpen ((J.comap f).subschemeι.app V.1 r) :=
  Scheme.preimage_basicOpen _ r

/-- Ambient principal restriction localizes the actual relative ring with its original map. -/
lemma relativeRestriction_basicOpen_isLocalization (V : X.affineOpens) (r : Γ(X, V.1)) :
    let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f U.1
    let := (relativeRestriction J f (U := U) (V := V)
      (homOfLE (X.basicOpen_le r))).toAlgebra
    IsLocalization.Away
      ((1 : IdealAdicGradedSections.Sections J ⊤) ⊗ₜ[Γ(Y, ⊤)] (J.comap f).subschemeι.app V.1 r)
      (RelativeAlgebra J f U) :=
  relativeRestriction_isLocalization J f _ _ (closedAffineChart_basicOpen J f V r)

end FLT.Mazur.IdealAdicGradedPullback
