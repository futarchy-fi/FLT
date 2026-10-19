/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.GaloisTensorReduced
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-!
# Reducedness under algebraic characteristic-zero coefficient extensions

An algebraic extension remains reduced after tensoring with any field.
Thus its spectrum morphism is geometrically reduced, including extensions
that are not finite. This applies to the original cubic coefficient cover.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.AlgebraicFieldExtensionReduced

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable (K L F : Type u) [Field K] [Field L] [Field F]
  [Algebra K L] [Algebra K F] [CharZero K] [Algebra.IsAlgebraic K L]

/-- Every field base change of the original algebraic extension is reduced. -/
theorem tensor_isReduced : _root_.IsReduced (F ⊗[K] L) := by
  apply IsReduced.tensorProduct_of_flat_of_forall_fg
  intro B hB
  let _ : Field B := B.isField_of_algebraic.toField
  let _ : Algebra.FiniteType K B := B.fg_iff_finiteType.mp hB
  let _ : Algebra.IsAlgebraic K B := Algebra.IsAlgebraic.of_injective B.val Subtype.val_injective
  let _ : Algebra.FormallyUnramified K B := Algebra.FormallyUnramified.of_isSeparable K B
  exact Algebra.FormallyUnramified.isReduced_of_field F (F ⊗[K] B)

omit [Field F] [Algebra K F] in
/-- The actual spectrum projection is geometrically reduced. -/
instance specMap_geometricallyReduced :
    GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  constructor
  intro F _ y Z fst snd H
  let a := (Spec.preimage y).hom
  let _ : Algebra K F := a.toAlgebra
  have hy : Spec.map (CommRingCat.ofHom (algebraMap K F)) = y := Spec.map_preimage y
  let T := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct K F L)
  have hr : _root_.IsReduced (F ⊗[K] L) := tensor_isReduced K L F
  let _ := hr
  have T' := T.flip
  rw [hy] at T'
  exact isReduced_of_isOpenImmersion (H.isoIsPullback _ _ T').hom

end FLT.Mazur.AlgebraicFieldExtensionReduced
