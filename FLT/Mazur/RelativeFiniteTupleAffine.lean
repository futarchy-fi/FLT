/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeOrderedTuples
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Affine finite relative tuple schemes

Explicit empty and successor comparisons identify the existing categorical
tuple schemes with iterated relative binary products. Hence affine sources
over an affine base have affine tuple schemes, including the empty tuple.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} (E : Over S)

/-- The empty relative tuple has the original base as its scheme. -/
def finZeroIso : tuples E (Fin 0) ≅ Over.mk (𝟙 S) where
  hom := Over.homMk (tuples E (Fin 0)).hom (by simp)
  inv := lift E (Fin 0) Fin.elim0
  hom_inv_id := by
    apply hom_ext
    intro i
    exact Fin.elim0 i
  inv_hom_id := by
    apply Over.OverMorphism.ext
    exact (lift E (Fin 0) Fin.elim0).w

/-- Split off the first label without changing any original coordinate. -/
def finSuccIso (n : ℕ) : tuples E (Fin (n + 1)) ≅ prod E (tuples E (Fin n)) where
  hom := prod.lift (coordinate E _ 0) (lift E _ fun i ↦ coordinate E _ i.succ)
  inv := lift E _ (Fin.cases prod.fst (fun i ↦ prod.snd ≫ coordinate E _ i))
  hom_inv_id := by
    apply hom_ext
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [coordinate, lift]
    · simp [coordinate, lift]
  inv_hom_id := by
    apply prod.hom_ext
    · simp [coordinate, lift]
    · apply hom_ext
      intro i
      simp [coordinate, lift]

/-- The binary relative product of affine schemes over an affine base is affine. -/
theorem affine_binary [IsAffine S] (A B : Over S) [IsAffine A.left] [IsAffine B.left] :
    IsAffine (prod A B).left := by
  exact IsAffine.of_isIso (Over.prodLeftIsoPullback A B).hom

/-- All finite tuple powers of an affine source are affine over the affine base. -/
theorem finTuples_affine [IsAffine S] [IsAffine E.left] (n : ℕ) :
    IsAffine (tuples E (Fin n)).left := by
  induction n with
  | zero =>
    let _ : IsAffine ((Over.forget S).obj (Over.mk (𝟙 S))) := ‹IsAffine S›
    exact IsAffine.of_isIso ((Over.forget S).mapIso (finZeroIso E)).hom
  | succ n ih =>
    let _ := ih
    let _ : IsAffine ((Over.forget S).obj (prod E (tuples E (Fin n)))) :=
      affine_binary E (tuples E (Fin n))
    exact IsAffine.of_isIso ((Over.forget S).mapIso (finSuccIso E n)).hom

end FLT.Mazur.RelativeOrderedTuples
