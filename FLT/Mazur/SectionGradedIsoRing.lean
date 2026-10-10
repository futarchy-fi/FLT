/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedIsoMultiplication
public import Mathlib.RingTheory.GradedAlgebra.RingHom

/-!
# The full graded section ring of an isomorphic line

Transport in every tensor degree gives an actual ring isomorphism. Its
homogeneous components retain the specified line comparison.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

namespace FLT.Mazur.SectionGradedIso

open FCurve ModuleLineBundleTensorPullback SectionGradedMultiplication SectionGradedSum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme} {L M : X.Modules} (e : L ≅ M) (U : X.Opens)

/-- Line transport on the full direct sum of all tensor degrees. -/
def sumMap : SectionGradedSum.Sections L U →+ SectionGradedSum.Sections M U :=
  DirectSum.toAddMonoid (fun n ↦ (DirectSum.of (Piece M U) n).comp
    (pieceMap e n U).toAddMonoidHom)

/-- The full direct-sum transport has the prescribed homogeneous component. -/
theorem sumMap_of (n : ℕ) (s : Piece L U n) :
    sumMap e U (of L U n s) = of M U n (pieceMap e n U s) :=
  DirectSum.toAddMonoid_of _ n s

/-- Line transport preserves multiplication on arbitrary finite sums of homogeneous sections. -/
theorem sumMap_product (a b : SectionGradedSum.Sections L U) :
    sumMap e U (product L U a b) = product M U (sumMap e U a) (sumMap e U b) := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of m s =>
    induction b using DirectSum.induction_on with
    | zero => simp
    | of n t =>
      change sumMap e U (product L U (of L U m s) (of L U n t)) =
        product M U (sumMap e U (of L U m s)) (sumMap e U (of L U n t))
      rw [product_of, sumMap_of, sumMap_of, sumMap_of, product_of, pieceMap_mul]
    | add b c hb hc => simp only [map_add, hb, hc]
  | add a c ha hc => simp only [map_add, LinearMap.add_apply, ha, hc]

/-- An actual ring homomorphism induced by the specified line isomorphism. -/
def ringHom : SectionGradedSum.Sections L U →+* SectionGradedSum.Sections M U where
  __ := sumMap e U
  map_one' := by
    change sumMap e U (of L U 0 (1 : Γ(X, U))) = of M U 0 (1 : Γ(X, U))
    rw [sumMap_of, pieceMap_zero]
  map_mul' a b := by
    simp only [mul_eq_product]
    exact sumMap_product e U a b

/-- Tensor powers preserve the actual inverse line comparison. -/
theorem tensorPowerCongr_symm (n : ℕ) :
    tensorPowerCongr e.symm n = (tensorPowerCongr e n).symm := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp only [tensorPowerCongr]
    rw [ih]
    rfl

/-- The inverse line comparison cancels on every actual tensor-degree section. -/
theorem pieceMap_symm_apply (n : ℕ) (s : Piece L U n) :
    pieceMap e.symm n U (pieceMap e n U s) = s := by
  have hh := congrArg (fun k ↦ k.app U s) (tensorPowerCongr e n).hom_inv_id
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, Hom.id_app,
    ConcreteCategory.id_apply] at hh
  unfold pieceMap
  rw [tensorPowerCongr_symm]
  exact hh

/-- Inverse line transport cancels on the whole section algebra. -/
theorem sumMap_symm_apply (s : SectionGradedSum.Sections L U) :
    sumMap e.symm U (sumMap e U s) = s := by
  induction s using DirectSum.induction_on with
  | zero => simp
  | of n s =>
    change sumMap e.symm U (sumMap e U (of L U n s)) = of L U n s
    rw [sumMap_of, sumMap_of, pieceMap_symm_apply]
  | add s t hs ht => simp only [map_add, hs, ht]

/-- The full ring equivalence retains all degrees and their specified section maps. -/
def ringEquiv : SectionGradedSum.Sections L U ≃+* SectionGradedSum.Sections M U where
  __ := ringHom e U
  invFun := sumMap e.symm U
  left_inv := sumMap_symm_apply e U
  right_inv := sumMap_symm_apply e.symm U

/-- The ring transport preserves every homogeneous submodule. -/
def gradedRingHom : grade L U →+*ᵍ grade M U where
  __ := ringHom e U
  map_mem := by
    intro n s hs
    obtain ⟨t, rfl⟩ := hs
    exact ⟨pieceMap e n U t, (sumMap_of e U n t).symm⟩

end FLT.Mazur.SectionGradedIso
