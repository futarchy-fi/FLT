/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedAlgebra

/-!
# Line isomorphisms preserve tensor-degree multiplication

An isomorphism of line sheaves transports every degree of its section ring.
The transport respects multiplication on all sections, by sheaf tensor
extensionality, without assuming that global sections are pure tensors.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

namespace FLT.Mazur.SectionGradedIso

open FCurve ModuleLineBundleTensorPullback ModuleSheafTensor
open SectionGradedMultiplication

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] ModuleSheafTensor.tensor

variable {X : Scheme} {L M : X.Modules} (e : L ≅ M)

/-- Transport actual tensor-power sections along the given line isomorphism. -/
def pieceMap (n : ℕ) (U : X.Opens) : Piece L U n →ₗ[Γ(X, U)] Piece M U n :=
  ((tensorPowerCongr e n).hom.val.app (.op U)).hom

/-- Degree casts commute with actual line transport. -/
theorem pieceMap_cast {m n : ℕ} (h : m = n) (U : X.Opens) (s : Piece L U m) :
    pieceMap e n U (cast L h U s) = cast M h U (pieceMap e m U s) := by
  subst n
  rfl

/-- Transport in degree zero fixes the structure module. -/
theorem pieceMap_zero (U : X.Opens) (r : Γ(X, U)) : pieceMap e 0 U r = r := rfl

/-- Transport carries the actual prepended tensor factor along the line isomorphism. -/
theorem pieceMap_cons (n : ℕ) (U : X.Opens) (s : Γ(L, U)) (t : Piece L U n) :
    pieceMap e (n + 1) U (cons L n U s t) =
      cons M n U (e.hom.app U s) (pieceMap e n U t) :=
  ModuleSheafTensor.map_pure _ _ _ _ _

/-- The canonical tensor-degree addition comparison is natural in a line isomorphism. -/
theorem addIso_naturality (m n : ℕ) :
    (tensorPowerAddIso L m n).hom ≫ (tensorPowerCongr e (m + n)).hom =
      ModuleSheafTensor.map (tensorPowerCongr e m).hom (tensorPowerCongr e n).hom ≫
        (tensorPowerAddIso M m n).hom := by
  induction m with
  | zero =>
    apply ModuleSheafTensor.hom_ext
    intro U r s
    simp only [Hom.comp_app, ConcreteCategory.comp_apply, ModuleSheafTensor.map_pure]
    change pieceMap e (0 + n) U (mul L U 0 n r s) =
      mul M U 0 n (pieceMap e 0 U r) (pieceMap e n U s)
    rw [SectionGradedMultiplication.zero_mul, pieceMap_cast, _root_.map_smul,
      pieceMap_zero, SectionGradedMultiplication.zero_mul]
  | succ m ih =>
    apply ModuleSheafTensorAssociator.left_hom_ext
    intro U a b c
    have hi := congrArg (fun k ↦ k.app U (pure _ _ U b c)) ih
    simp only [Hom.comp_app, ConcreteCategory.comp_apply, ModuleSheafTensor.map_pure] at hi
    change pieceMap e (m + n) U (mul L U m n b c) =
      mul M U m n (pieceMap e m U b) (pieceMap e n U c) at hi
    simp only [Hom.comp_app, ConcreteCategory.comp_apply]
    erw [ModuleSheafTensor.map_pure (tensorPowerCongr e (m + 1)).hom
      (tensorPowerCongr e n).hom]
    change pieceMap e (m + 1 + n) U (mul L U (m + 1) n (cons L m U a b) c) =
      mul M U (m + 1) n (pieceMap e (m + 1) U (cons L m U a b)) (pieceMap e n U c)
    rw [succ_mul_pure, pieceMap_cast, pieceMap_cons, hi, pieceMap_cons, succ_mul_pure]

/-- All homogeneous section products commute with line transport. -/
theorem pieceMap_mul (U : X.Opens) (m n : ℕ) (s : Piece L U m) (t : Piece L U n) :
    pieceMap e (m + n) U (mul L U m n s t) =
      mul M U m n (pieceMap e m U s) (pieceMap e n U t) := by
  have hh := congrArg (fun k ↦ k.app U (pure _ _ U s t)) (addIso_naturality e m n)
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, ModuleSheafTensor.map_pure] at hh
  exact hh

end FLT.Mazur.SectionGradedIso
