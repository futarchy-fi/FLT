/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFiberKernels
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The three actual affine-line closed subschemes

Each original factor defines precisely its oriented polynomial line, including
its scheme structure. The closed immersions jointly cover the entire fiber.
-/

@[expose] public noncomputable section

open Polynomial AlgebraicGeometry

namespace FLT.Mazur.WeierstrassModificationX

set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R] (a : R)

/-- The incidence quotient is the polynomial line with free coordinate v. -/
def fiberCentralQuotientEquiv :
    (FiberCoordinate a 0 ⧸ Ideal.span {fiberT a 0}) ≃ₐ[R] R[X] :=
  (Ideal.quotientEquivAlgOfEq R (fiberCentralLine_ker a).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (fiberCentralLine_surjective a))

/-- The first tangent quotient is the polynomial line with free coordinate t. -/
def fiberFirstQuotientEquiv :
    (FiberCoordinate a 0 ⧸ Ideal.span {fiberV a 0}) ≃ₐ[R] R[X] :=
  (Ideal.quotientEquivAlgOfEq R (fiberFirstLine_ker a).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (fiberFirstLine_surjective a))

/-- The second tangent quotient retains its original slope -a. -/
def fiberSecondQuotientEquiv :
    (FiberCoordinate a 0 ⧸ Ideal.span {fiberV a 0 + algebraMap R _ a}) ≃ₐ[R] R[X] :=
  (Ideal.quotientEquivAlgOfEq R (fiberSecondLine_ker a).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (fiberSecondLine_surjective a))

/-- The central quotient comparison is induced by the original branch map. -/
@[simp] theorem fiberCentralQuotientEquiv_mk (z : FiberCoordinate a 0) :
    fiberCentralQuotientEquiv a (Ideal.Quotient.mk _ z) = fiberCentralLine a z := by
  rw [fiberCentralQuotientEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk]
  exact Ideal.quotientKerAlgEquivOfSurjective_mk (fiberCentralLine_surjective a) z

/-- The first quotient comparison is induced by the original branch map. -/
@[simp] theorem fiberFirstQuotientEquiv_mk (z : FiberCoordinate a 0) :
    fiberFirstQuotientEquiv a (Ideal.Quotient.mk _ z) = fiberFirstLine a z := by
  rw [fiberFirstQuotientEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk]
  exact Ideal.quotientKerAlgEquivOfSurjective_mk (fiberFirstLine_surjective a) z

/-- The second quotient comparison is induced by the original branch map. -/
@[simp] theorem fiberSecondQuotientEquiv_mk (z : FiberCoordinate a 0) :
    fiberSecondQuotientEquiv a (Ideal.Quotient.mk _ z) = fiberSecondLine a z := by
  rw [fiberSecondQuotientEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk]
  exact Ideal.quotientKerAlgEquivOfSurjective_mk (fiberSecondLine_surjective a) z

/-- The original incidence line inside the full horizontal fiber. -/
def fiberCentralImmersion : Spec (.of R[X]) ⟶ Spec (.of (FiberCoordinate a 0)) :=
  Spec.map (CommRingCat.ofHom (fiberCentralLine a).toRingHom)

/-- The original first tangent line inside the full horizontal fiber. -/
def fiberFirstImmersion : Spec (.of R[X]) ⟶ Spec (.of (FiberCoordinate a 0)) :=
  Spec.map (CommRingCat.ofHom (fiberFirstLine a).toRingHom)

/-- The original second tangent line inside the full horizontal fiber. -/
def fiberSecondImmersion : Spec (.of R[X]) ⟶ Spec (.of (FiberCoordinate a 0)) :=
  Spec.map (CommRingCat.ofHom (fiberSecondLine a).toRingHom)

instance fiberCentralImmersion_isClosedImmersion : IsClosedImmersion (fiberCentralImmersion a) :=
  IsClosedImmersion.spec_of_surjective _ (fiberCentralLine_surjective a)

instance fiberFirstImmersion_isClosedImmersion : IsClosedImmersion (fiberFirstImmersion a) :=
  IsClosedImmersion.spec_of_surjective _ (fiberFirstLine_surjective a)

instance fiberSecondImmersion_isClosedImmersion : IsClosedImmersion (fiberSecondImmersion a) :=
  IsClosedImmersion.spec_of_surjective _ (fiberSecondLine_surjective a)

/-- The incidence immersion has exactly the original incidence-zero support. -/
theorem range_fiberCentralImmersion : Set.range (fiberCentralImmersion a) =
    PrimeSpectrum.zeroLocus (Ideal.span {fiberT a 0}) := by
  rw [← fiberCentralLine_ker]
  exact range_comap_of_surjective _ _ (fiberCentralLine_surjective a)

/-- The first tangent immersion has exactly the slope-zero support. -/
theorem range_fiberFirstImmersion : Set.range (fiberFirstImmersion a) =
    PrimeSpectrum.zeroLocus (Ideal.span {fiberV a 0}) := by
  rw [← fiberFirstLine_ker]
  exact range_comap_of_surjective _ _ (fiberFirstLine_surjective a)

/-- The second tangent immersion has exactly the translated-slope-zero support. -/
theorem range_fiberSecondImmersion : Set.range (fiberSecondImmersion a) =
    PrimeSpectrum.zeroLocus (Ideal.span {fiberV a 0 + algebraMap R _ a}) := by
  rw [← fiberSecondLine_ker]
  exact range_comap_of_surjective _ _ (fiberSecondLine_surjective a)

/-- The three actual closed subschemes cover the full horizontal fiber. -/
theorem fiber_closed_branches_cover (p : Spec (.of (FiberCoordinate a 0))) :
    p ∈ Set.range (fiberCentralImmersion a) ∨
      p ∈ Set.range (fiberFirstImmersion a) ∨ p ∈ Set.range (fiberSecondImmersion a) := by
  rw [range_fiberCentralImmersion, range_fiberFirstImmersion, range_fiberSecondImmersion]
  change Ideal.span {fiberT a 0} ≤ p.asIdeal ∨ Ideal.span {fiberV a 0} ≤ p.asIdeal ∨
    Ideal.span {fiberV a 0 + algebraMap R _ a} ≤ p.asIdeal
  rcases fiber_prime_branches a p with h | h | h
  · exact Or.inl (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h))
  · exact Or.inr (Or.inl (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h)))
  · exact Or.inr (Or.inr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h)))

end FLT.Mazur.WeierstrassModificationX
