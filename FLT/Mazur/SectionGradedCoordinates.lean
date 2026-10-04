/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedRing
public import FLT.Mazur.TensorPowerGeneratorOpen

/-!
# Multiplication in line-bundle coordinates

A chosen sheaf trivialization identifies multiplication of arbitrary
sections in all tensor degrees with multiplication of their coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SectionGradedCoordinates
open FCurve ModuleLineBundleTensorPullback ModuleSheafTensor
open SectionGradedMultiplication
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} {L : X.Modules} (e : L ≅ structureModule X)

/-- The structure-module tensor pairing is ring multiplication. -/
lemma scalar_pure (U : X.Opens) (r s : Γ(X, U)) :
    (leftUnitor (structureModule X)).hom.app U
      (pure (structureModule X) (structureModule X) U r s) = r * s :=
  leftUnitor_pure (structureModule X) U r s

/-- Coordinate of a section in the induced tensor-power trivialization. -/
def coordinate (n : ℕ) (U : X.Opens) (s : Piece L U n) : Γ(X, U) :=
  (tensorPowerTrivialization e n).hom.app U s

/-- Coordinates do not depend on how an equal degree is written. -/
lemma coordinate_cast {m n : ℕ} (h : m = n) (U : X.Opens) (s : Piece L U m) :
    coordinate e n U (cast L h U s) = coordinate e m U s := by
  subst n
  rfl

/-- Coordinates multiply on a pure first tensor factor. -/
lemma coordinate_cons (n : ℕ) (U : X.Opens) (s : Γ(L, U)) (t : Piece L U n) :
    coordinate e (n + 1) U (cons L n U s t) =
      (show Γ(X, U) from e.hom.app U s) * coordinate e n U t :=
  trivialTensorIso_pure e (tensorPowerTrivialization e n) U s t

/-- Addition of degrees becomes scalar multiplication under the trivializations. -/
lemma addIso_coordinate (m n : ℕ) :
    (tensorPowerAddIso L m n).hom ≫ (tensorPowerTrivialization e (m + n)).hom =
      ModuleSheafTensor.map (tensorPowerTrivialization e m).hom
        (tensorPowerTrivialization e n).hom ≫ (leftUnitor (structureModule X)).hom := by
  induction m with
  | zero =>
    apply ModuleSheafTensor.hom_ext
    intro U r s
    change Γ(X, U) at r
    simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      ModuleSheafTensor.map_pure]
    change coordinate e (0 + n) U (mul L U 0 n r s) =
      (leftUnitor (structureModule X)).hom.app U
      (pure (structureModule X) (structureModule X) U r (coordinate e n U s))
    rw [SectionGradedMultiplication.zero_mul, coordinate_cast, scalar_pure]
    exact Hom.app_smul (tensorPowerTrivialization e n).hom r s
  | succ m ih =>
    apply ModuleSheafTensorAssociator.left_hom_ext
    intro U a b c
    dsimp only [tensorPower, tensorPowerTrivialization]
    simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      ModuleSheafTensor.map_pure]
    have hi := congrArg (fun f ↦ f.app U (pure _ _ U b c)) ih
    simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      ModuleSheafTensor.map_pure] at hi
    change coordinate e (m + n) U (mul L U m n b c) =
      (leftUnitor (structureModule X)).hom.app U
      (pure (structureModule X) (structureModule X) U (coordinate e m U b)
        (coordinate e n U c)) at hi
    rw [scalar_pure] at hi
    change coordinate e (m + 1 + n) U (mul L U (m + 1) n (cons L m U a b) c) =
      (leftUnitor (structureModule X)).hom.app U
      (pure (structureModule X) (structureModule X) U (coordinate e (m + 1) U (cons L m U a b))
        (coordinate e n U c))
    rw [succ_mul_pure, coordinate_cast, coordinate_cons, scalar_pure,
      coordinate_cons, hi]
    exact (_root_.mul_assoc _ _ _).symm

/-- The coordinate formula holds for all sections, not just pure tensor powers. -/
lemma coordinate_mul (m n : ℕ) (U : X.Opens) (s : Piece L U m) (t : Piece L U n) :
    coordinate e (m + n) U (mul L U m n s t) =
      coordinate e m U s * coordinate e n U t := by
  have h := congrArg (fun f ↦ f.app U (pure _ _ U s t)) (addIso_coordinate e m n)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    ModuleSheafTensor.map_pure] at h
  change coordinate e (m + n) U (mul L U m n s t) =
    (leftUnitor (structureModule X)).hom.app U
      (pure (structureModule X) (structureModule X) U
        (coordinate e m U s) (coordinate e n U t)) at h
  rw [scalar_pure] at h
  exact h

/-- Coordinates detect equality of arbitrary tensor-power sections. -/
lemma coordinate_injective (n : ℕ) (U : X.Opens) : Function.Injective (coordinate e n U) := by
  intro s t h
  have h' := congrArg ((tensorPowerTrivialization e n).inv.app U) h
  simpa only [coordinate, ← ConcreteCategory.comp_apply, ← Hom.comp_app,
    Iso.hom_inv_id, Hom.id_app, ConcreteCategory.id_apply] using h'

include e in
/-- A trivial line bundle has commutative tensor-degree multiplication. -/
lemma mul_comm (m n : ℕ) (U : X.Opens) (s : Piece L U m) (t : Piece L U n) :
    mul L U m n s t = cast L (Nat.add_comm n m) U (mul L U n m t s) := by
  apply coordinate_injective e (m + n) U
  rw [coordinate_cast, coordinate_mul, coordinate_mul, _root_.mul_comm]

end FLT.Mazur.SectionGradedCoordinates
