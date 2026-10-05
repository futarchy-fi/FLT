/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicGradedClosedAction
public import FLT.Mazur.IdealAdicGradedDegreeZeroGeneration
public import Mathlib.Algebra.Module.TransferInstance

/-!
# The total closed graded coefficient module

The direct sum of the actual closed coefficients carries the graded base
module structure. Its canonical comparison with the ambient coefficients
is linear, and homogeneous scalar multiplication is the original descended
sheaf action. Opens here are inverse images of ambient opens.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.IdealAdicQuotient FLT.Mazur.IdealAdicGradedSections
open FLT.Mazur.IdealAdicGradedPullback
open scoped DirectSum

universe u

namespace FLT.Mazur.IdealAdicGradedClosedAction

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)

/-- Sections of an actual closed coefficient over the inverse image of an ambient open. -/
abbrev ClosedPiece (U : X.Opens) (n : ℕ) : Type u :=
  Γ(closedIdealGraded I n, I.subschemeι ⁻¹ᵁ U)

/-- The closed pushforward comparison identifies actual coefficient sections. -/
def pieceEquiv (U : X.Opens) (n : ℕ) : ClosedPiece I U n ≃+ Piece I U n :=
  ((SheafOfModules.evaluation X.ringCatSheaf (.op U)).mapIso
    (closedIdealGradedIso I n)).toLinearEquiv.toAddEquiv

/-- The full direct sum of the actual closed graded coefficients. -/
abbrev Total (U : X.Opens) := ⨁ n : ℕ, ClosedPiece I U n

/-- The actual closed comparisons identify the full direct sums. -/
def totalEquiv (U : X.Opens) : Total I U ≃+ IdealAdicGradedSections.Sections I U :=
  DirectSum.congrAddEquiv (pieceEquiv I U)

/-- The total comparison retains each original homogeneous closed comparison. -/
lemma totalEquiv_of (U : X.Opens) (n : ℕ) (t : ClosedPiece I U n) :
    totalEquiv I U (DirectSum.of (ClosedPiece I U) n t) =
      of I U n (pieceEquiv I U n t) := by
  exact DirectSum.map_of (fun n ↦ (pieceEquiv I U n).toAddMonoidHom) n t

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

/-- The actual base graded algebra acts on the total closed coefficient module. -/
@[instance_reducible]
def baseModule (U : X.Opens) :
    Module (IdealAdicGradedSections.Sections J ⊤) (Total (J.comap f) U) :=
  let := localBaseAlgebra J f U
  (totalEquiv (J.comap f) U).module _

/-- The canonical total closed comparison is linear over the actual graded base algebra. -/
def baseLinearEquiv (U : X.Opens) :
    let := localBaseAlgebra J f U
    let := baseModule J f U
    Total (J.comap f) U ≃ₗ[IdealAdicGradedSections.Sections J ⊤]
      IdealAdicGradedSections.Sections (J.comap f) U :=
  let := localBaseAlgebra J f U
  (totalEquiv (J.comap f) U).linearEquiv _

/-- Homogeneous multiplication is the original closed sheaf action on every such open. -/
lemma baseModule_smul_of (U : X.Opens) (a n : ℕ) (s : Piece J ⊤ a)
    (t : ClosedPiece (J.comap f) U n) :
    let := baseModule J f U
    of J ⊤ a s • DirectSum.of (ClosedPiece (J.comap f) U) n t =
      DirectSum.of (ClosedPiece (J.comap f) U) (a + n)
        ((baseAction J f a n s).app ((J.comap f).subschemeι ⁻¹ᵁ U) t) := by
  let := localBaseAlgebra J f U
  let := baseModule J f U
  apply (totalEquiv (J.comap f) U).injective
  change totalEquiv (J.comap f) U ((totalEquiv (J.comap f) U).symm
    (localRingHom J f U (of J ⊤ a s) *
      totalEquiv (J.comap f) U (DirectSum.of (ClosedPiece (J.comap f) U) n t))) = _
  rw [AddEquiv.apply_symm_apply, totalEquiv_of, totalEquiv_of, localRingHom_of, mul_of]
  congr 1
  have h := congrArg (fun k ↦ k.app U t) (baseAction_comparison J f a n s)
  change pieceEquiv (J.comap f) U (a + n)
    ((baseAction J f a n s).app ((J.comap f).subschemeι ⁻¹ᵁ U) t) =
      (sectionAction (J.comap f) a n (pull J f a ⊤ s)).app U
        (pieceEquiv (J.comap f) U n t) at h
  exact h.symm

/-- The total closed coefficient is generated in degree zero on every ambient affine chart. -/
lemma closedDegreeZero_span (U : X.affineOpens) :
    let := baseModule J f U.1
    Submodule.span (IdealAdicGradedSections.Sections J ⊤)
      (Set.range (DirectSum.of (ClosedPiece (J.comap f) U.1) 0)) = ⊤ := by
  let := localBaseAlgebra J f U.1
  let := baseModule J f U.1
  let e := baseLinearEquiv J f U.1
  apply Submodule.map_injective_of_injective e.injective
  rw [Submodule.map_span, Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective]
  have hi : e '' Set.range (DirectSum.of (ClosedPiece (J.comap f) U.1) 0) =
      Set.range (of (J.comap f) U.1 0) := by
    ext x
    constructor
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨pieceEquiv (J.comap f) U.1 0 t, (totalEquiv_of (J.comap f) U.1 0 t).symm⟩
    · rintro ⟨t, rfl⟩
      obtain ⟨t, rfl⟩ := (pieceEquiv (J.comap f) U.1 0).surjective t
      exact ⟨DirectSum.of (ClosedPiece (J.comap f) U.1) 0 t, ⟨t, rfl⟩,
        totalEquiv_of (J.comap f) U.1 0 t⟩
  change Submodule.span (IdealAdicGradedSections.Sections J ⊤)
    (e '' Set.range (DirectSum.of (ClosedPiece (J.comap f) U.1) 0)) = ⊤
  rw [hi]
  exact degreeZero_span J f U

end FLT.Mazur.IdealAdicGradedClosedAction
