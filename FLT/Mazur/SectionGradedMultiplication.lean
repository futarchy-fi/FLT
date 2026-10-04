/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorPowerReassociation
public import FLT.Mazur.ModuleTensorPowerSection

/-!
# Multiplication of sections of tensor powers

The multiplication uses the actual sheaf tensor and its exponent-addition
isomorphism. It is bilinear on every open and commutes with restriction.
This is the multiplication input for the full graded section algebra;
no ring structure or Proj morphism is asserted in this module.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SectionGradedMultiplication
open FCurve ModuleLineBundleTensorPullback ModuleSheafTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} (L : X.Modules)

/-- Degree `n` consists of all sections of the actual `n`th tensor power. -/
abbrev Piece (U : X.Opens) (n : ℕ) : Type u := Γ(tensorPower L n, U)

/-- The bilinear multiplication from degrees `m`, `n` to degree `m + n`. -/
def mul (U : X.Opens) (m n : ℕ) :
    Piece L U m →ₗ[Γ(X, U)] Piece L U n →ₗ[Γ(X, U)] Piece L U (m + n) :=
  ((pairing (tensorPower L m) (tensorPower L n)).app U).compr₂
    ((tensorPowerAddIso L m n).hom.val.app (.op U)).hom

/-- The multiplication is the exponent-addition isomorphism on a pure tensor. -/
lemma mul_apply (U : X.Opens) (m n : ℕ) (s : Piece L U m) (t : Piece L U n) :
    mul L U m n s t = (tensorPowerAddIso L m n).hom.app U
      (pure (tensorPower L m) (tensorPower L n) U s t) := rfl

/-- Restriction preserves the product in every pair of degrees. -/
lemma mul_restrict {U V : X.Opens} (i : U ⟶ V) (m n : ℕ)
    (s : Piece L V m) (t : Piece L V n) :
    (tensorPower L (m + n)).presheaf.map i.op (mul L V m n s t) =
      mul L U m n ((tensorPower L m).presheaf.map i.op s)
        ((tensorPower L n).presheaf.map i.op t) := by
  have h := congrArg (fun k ↦ k (pure (tensorPower L m) (tensorPower L n) V s t))
    ((tensorPowerAddIso L m n).hom.mapPresheaf.naturality i.op)
  change (tensorPowerAddIso L m n).hom.app U
    ((tensor (tensorPower L m) (tensorPower L n)).presheaf.map i.op
      (pure _ _ V s t)) = _ at h
  rw [pure_restrict] at h
  exact h.symm

/-- Products depend additively on the left section. -/
lemma add_mul (U : X.Opens) (m n : ℕ) (s s' : Piece L U m) (t : Piece L U n) :
    mul L U m n (s + s') t = mul L U m n s t + mul L U m n s' t := by
  exact LinearMap.congr_fun (map_add (mul L U m n) s s') t

/-- Products depend additively on the right section. -/
lemma mul_add (U : X.Opens) (m n : ℕ) (s : Piece L U m) (t t' : Piece L U n) :
    mul L U m n s (t + t') = mul L U m n s t + mul L U m n s t' :=
  map_add (mul L U m n s) t t'

/-- Base scalars may be pulled out of either input simultaneously. -/
lemma smul_mul_smul (U : X.Opens) (m n : ℕ) (a b : Γ(X, U))
    (s : Piece L U m) (t : Piece L U n) :
    mul L U m n (a • s) (b • t) = (a * b) • mul L U m n s t := by
  rw [LinearMap.map_smul₂, _root_.map_smul, smul_smul]

/-- Equal degrees transport the corresponding pure powers. -/
lemma cast_power (U : X.Opens) (s : Γ(L, U)) {m n : ℕ} (h : m = n) :
    (eqToIso (congrArg (tensorPower L) h)).hom.app U (tensorPowerSection L U s m) =
      tensorPowerSection L U s n := by
  subst n
  rfl

/-- Multiplying two powers of one section adds their exponents, including zero. -/
lemma mul_power (U : X.Opens) (s : Γ(L, U)) (m n : ℕ) :
    mul L U m n (tensorPowerSection L U s m) (tensorPowerSection L U s n) =
      tensorPowerSection L U s (m + n) := by
  induction m with
  | zero =>
    change (eqToIso (congrArg (tensorPower L) (Nat.zero_add n).symm)).hom.app U
      ((leftUnitor _).hom.app U
      (pure _ _ U (1 : Γ(X, U)) (tensorPowerSection L U s n))) = _
    rw [leftUnitor_pure, one_smul]
    exact cast_power L U s (Nat.zero_add n).symm
  | succ m ih =>
    change (eqToIso (congrArg (tensorPower L)
      (show m + n + 1 = m + 1 + n by omega))).hom.app U
      ((map (𝟙 L) (tensorPowerAddIso L m n).hom).app U
      ((ModuleSheafTensorAssociator.associator _ _ _).hom.app U
        (pure _ _ U (pure _ _ U s (tensorPowerSection L U s m))
          (tensorPowerSection L U s n)))) = _
    rw [ModuleSheafTensorAssociator.associator_hom_pure, map_pure]
    change (eqToIso (congrArg (tensorPower L)
      (show m + n + 1 = m + 1 + n by omega))).hom.app U (pure _ _ U s (mul L U m n
      (tensorPowerSection L U s m) (tensorPowerSection L U s n))) = _
    rw [ih]
    exact cast_power L U s (by omega)

end FLT.Mazur.SectionGradedMultiplication
