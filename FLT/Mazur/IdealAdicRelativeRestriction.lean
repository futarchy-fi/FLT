/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicGradedRestriction
public import FLT.Mazur.IdealAdicRelativeGradedAlgebra
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Restriction of the relative graded coefficient algebra

The relative tensor algebras restrict along inclusions of ambient affine
charts, and their surjections to the actual coefficient algebras commute
with those restrictions. The fixed graded base algebra is preserved.
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

local notation "GradedSections" => IdealAdicGradedSections.Sections

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y] in
/-- Ordinary base scalars restrict through the actual source structure sheaf. -/
lemma localScalarMap_restrict {U V : X.Opens} (i : U ⟶ V) (r : Γ(Y, ⊤)) :
    X.presheaf.map i.op (localScalarMap f V r) = localScalarMap f U r := by
  change X.presheaf.map i.op
    (X.presheaf.map (homOfLE (by simp : V ≤ f ⁻¹ᵁ ⊤)).op (f.app ⊤ r)) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y] in
/-- Closed coordinate restriction preserves the actual map from ordinary base scalars. -/
lemma closedBaseMap_restrict {U V : X.Opens} (i : U ⟶ V) (r : Γ(Y, ⊤)) :
    closedScalarRestriction (J.comap f) i (closedBaseMap J f V r) =
      closedBaseMap J f U r := by
  have h := congrArg (fun k ↦ k (localScalarMap f V r)) ((J.comap f).subschemeι.naturality i.op)
  change (J.comap f).subschemeι.app U (X.presheaf.map i.op (localScalarMap f V r)) = _ at h
  rw [localScalarMap_restrict] at h
  exact h.symm

/-- Closed coordinate restriction is an algebra map over the original base ring. -/
def closedRestrictionAlgHom {U V : X.Opens} (i : U ⟶ V) :
    let := closedBaseAlgebra J f V
    let := closedBaseAlgebra J f U
    ClosedScalars (J.comap f) V →ₐ[Γ(Y, ⊤)] ClosedScalars (J.comap f) U := by
  let := closedBaseAlgebra J f V
  let := closedBaseAlgebra J f U
  exact { closedScalarRestriction (J.comap f) i with
    commutes' := closedBaseMap_restrict J f i }

/-- Relative tensor algebras restrict by the actual closed coordinate restriction. -/
def relativeRestriction {U V : X.affineOpens} (i : U.1 ⟶ V.1) :
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f U.1
    RelativeAlgebra J f V →ₐ[GradedSections J ⊤] RelativeAlgebra J f U := by
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f U.1
  exact Algebra.TensorProduct.map (AlgHom.id (GradedSections J ⊤) _)
    (closedRestrictionAlgHom J f i)

omit [IsLocallyNoetherian X] [IsAffine Y] in
/-- Relative restriction retains the original base section and closed coordinate restriction. -/
lemma relativeRestriction_tmul {U V : X.affineOpens} (i : U.1 ⟶ V.1)
    (a : GradedSections J ⊤) (r : ClosedScalars (J.comap f) V.1) :
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f U.1
    relativeRestriction J f i (a ⊗ₜ[Γ(Y, ⊤)] r) =
      a ⊗ₜ[Γ(Y, ⊤)] closedScalarRestriction (J.comap f) i r := by
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f U.1
  exact Algebra.TensorProduct.map_tmul _ _ a r

/-- The actual relative quotient maps commute with affine restriction. -/
lemma relativeMap_restrict {U V : X.affineOpens} (i : U.1 ⟶ V.1) :
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f U.1
    let := localBaseAlgebra J f V.1
    let := localBaseAlgebra J f U.1
    ∀ x : RelativeAlgebra J f V,
      restrictRingHom (J.comap f) U.1 i (relativeMap J f V x) =
        relativeMap J f U (relativeRestriction J f i x) := by
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f U.1
  let := localBaseAlgebra J f V.1
  let := localBaseAlgebra J f U.1
  dsimp only
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a r =>
    rw [relativeRestriction_tmul, relativeMap_tmul, relativeMap_tmul]
    change restrictRingHom (J.comap f) U.1 i
      (localRingHom J f V.1 a * closedScalarAdd (J.comap f) V.1 r) =
        localRingHom J f U.1 a * closedScalarAdd (J.comap f) U.1
          (closedScalarRestriction (J.comap f) i r)
    rw [map_mul]
    exact congrArg₂ (· * ·) (RingHom.congr_fun (localRingHom_restrict J f i) a)
      (closedScalarAdd_restrict (J.comap f) i r)
  | add x y hx hy => simp only [map_add, hx, hy]

end FLT.Mazur.IdealAdicGradedPullback
