/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicClosedScalar
public import FLT.Mazur.IdealAdicGradedDegreeZeroGeneration
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The relative graded algebra on a closed affine chart

Tensor the actual graded base algebra with the actual closed coordinate ring
over the original base ring. The canonical map to all actual coefficients
is surjective. The closed coordinate ring is essential in this statement.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.IdealAdicGradedSections
open scoped TensorProduct

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

local notation "GradedSections" => IdealAdicGradedSections.Sections

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

/-- Restrict ordinary base scalars to the actual source open. -/
def localScalarMap (U : X.Opens) : Γ(Y, ⊤) →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE (by simp : U ≤ f ⁻¹ᵁ ⊤)).op).hom.comp (f.app ⊤).hom

/-- The local graded comparison preserves the original base scalars. -/
lemma localRingHom_scalar (U : X.Opens) (r : Γ(Y, ⊤)) :
    localRingHom J f U (algebraMap Γ(Y, ⊤) (GradedSections J ⊤) r) =
      algebraMap Γ(X, U) (GradedSections (J.comap f) U) (localScalarMap f U r) := by
  change localRingHom J f U (of J ⊤ 0 (scalar J ⊤ r)) =
    of (J.comap f) U 0 (scalar (J.comap f) U (localScalarMap f U r))
  rw [localRingHom_of]
  congr 1
  unfold gradedSection
  rw [pull_scalar, scalar_restrict]
  rfl

/-- Ordinary base scalars map to the actual closed coordinate ring. -/
def closedBaseMap (U : X.Opens) : Γ(Y, ⊤) →+* ClosedScalars (J.comap f) U :=
  ((J.comap f).subschemeι.app U).hom.comp (localScalarMap f U)

/-- The closed coordinate ring is an algebra over the original base ring. -/
@[instance_reducible]
def closedBaseAlgebra (U : X.Opens) : Algebra Γ(Y, ⊤) (ClosedScalars (J.comap f) U) :=
  (closedBaseMap J f U).toAlgebra

/-- Ordinary base scalars act through the actual graded comparison. -/
@[instance_reducible]
def totalBaseScalarAlgebra (U : X.Opens) : Algebra Γ(Y, ⊤) (GradedSections (J.comap f) U) :=
  ((localRingHom J f U).comp (algebraMap Γ(Y, ⊤) (GradedSections J ⊤))).toAlgebra

variable (U : X.affineOpens)

/-- Closed scalars map to the actual coefficient algebra over the original base ring. -/
def closedScalarAlgHom :
    let := closedBaseAlgebra J f U.1
    let := totalBaseScalarAlgebra J f U.1
    ClosedScalars (J.comap f) U.1 →ₐ[Γ(Y, ⊤)] GradedSections (J.comap f) U.1 := by
  let := closedBaseAlgebra J f U.1
  let := totalBaseScalarAlgebra J f U.1
  refine { closedScalarRingHom (J.comap f) U with commutes' := ?_ }
  intro r
  change closedScalarAdd (J.comap f) U.1
    ((J.comap f).subschemeι.app U.1 (localScalarMap f U.1 r)) =
      localRingHom J f U.1 (algebraMap Γ(Y, ⊤) (GradedSections J ⊤) r)
  rw [closedScalarAdd_quotient, localRingHom_scalar]

/-- The relative coefficient algebra uses the actual closed coordinate ring. -/
abbrev RelativeAlgebra :=
  let := closedBaseAlgebra J f U.1
  GradedSections J ⊤ ⊗[Γ(Y, ⊤)] ClosedScalars (J.comap f) U.1

/-- The relative algebra maps to the actual total coefficient algebra. -/
def relativeMap :
    let := closedBaseAlgebra J f U.1
    let := localBaseAlgebra J f U.1
    RelativeAlgebra J f U →ₐ[GradedSections J ⊤] GradedSections (J.comap f) U.1 := by
  let := closedBaseAlgebra J f U.1
  let := totalBaseScalarAlgebra J f U.1
  let := localBaseAlgebra J f U.1
  let : IsScalarTower Γ(Y, ⊤) (GradedSections J ⊤) (GradedSections (J.comap f) U.1) :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  exact (AlgHom.liftEquiv Γ(Y, ⊤) (GradedSections J ⊤) _ _) (closedScalarAlgHom J f U)

/-- Pure tensors act by the original graded base action on a closed structure scalar. -/
lemma relativeMap_tmul (a : GradedSections J ⊤) (r : ClosedScalars (J.comap f) U.1) :
    let := closedBaseAlgebra J f U.1
    let := localBaseAlgebra J f U.1
    relativeMap J f U (a ⊗ₜ[Γ(Y, ⊤)] r) = a • closedScalarAdd (J.comap f) U.1 r := rfl

/-- The relative algebra surjects onto all degrees of the actual coefficient algebra. -/
lemma relativeMap_surjective :
    let := closedBaseAlgebra J f U.1
    let := localBaseAlgebra J f U.1
    Function.Surjective (relativeMap J f U) := by
  let := closedBaseAlgebra J f U.1
  let := localBaseAlgebra J f U.1
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← degreeZero_span J f U]
  apply Submodule.span_le.mpr
  rintro _ ⟨s, rfl⟩
  refine ⟨1 ⊗ₜ[Γ(Y, ⊤)] zeroSectionEquiv (J.comap f) U.1 s, ?_⟩
  change relativeMap J f U (1 ⊗ₜ[Γ(Y, ⊤)] zeroSectionEquiv (J.comap f) U.1 s) = _
  rw [relativeMap_tmul, one_smul]
  change of (J.comap f) U.1 0
    ((zeroSectionEquiv (J.comap f) U.1).symm (zeroSectionEquiv (J.comap f) U.1 s)) = _
  rw [AddEquiv.symm_apply_apply]

/-- The actual coefficient algebra is finite as a module over the relative algebra. -/
lemma relativeMap_finite :
    let := closedBaseAlgebra J f U.1
    let := localBaseAlgebra J f U.1
    (relativeMap J f U).Finite := by
  let := closedBaseAlgebra J f U.1
  let := localBaseAlgebra J f U.1
  exact AlgHom.Finite.of_surjective _ (relativeMap_surjective J f U)

end FLT.Mazur.IdealAdicGradedPullback
