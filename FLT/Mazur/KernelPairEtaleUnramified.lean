/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-!
# Unramified geometry detected by a full etale kernel relation

An etale endpoint of the full kernel pair makes the diagonal an etale
monomorphism. Thus the projection is formally unramified without assuming
flatness, surjectivity, or a reduced target.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.KernelPairEtaleGeometry
variable {D A T : Scheme.{u}} (p q : D ⟶ A) (w : A ⟶ T)

/-- An etale first kernel projection forces an open diagonal on the original morphism. -/
theorem diagonal_isOpenImmersion [Etale (pullback.fst w w)] :
    IsOpenImmersion (pullback.diagonal w) := by
  let _ : Etale (pullback.diagonal w ≫ pullback.fst w w) := by
    rw [pullback.diagonal_fst]
    infer_instance
  let _ := Etale.of_comp (pullback.diagonal w) (pullback.fst w w)
  exact IsOpenImmersion.of_flat_of_mono _

/-- A full original kernel relation proves unramifiedness before any flatness argument. -/
theorem formallyUnramified (H : IsPullback p q w w) [Etale p] :
    FormallyUnramified w := by
  let _ : Etale (pullback.fst w w) := by
    rw [← H.isoPullback_inv_fst]
    infer_instance
  let _ := diagonal_isOpenImmersion w
  infer_instance

/-- Actual flatness upgrades the recovered unramified geometry to etaleness. -/
theorem etale (H : IsPullback p q w w) [Etale p] [Flat w]
    [LocallyOfFinitePresentation w] : Etale w := by
  let _ := formallyUnramified p q w H
  exact Etale.of_formallyUnramified_of_flat _

end FLT.Mazur.KernelPairEtaleGeometry
