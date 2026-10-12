/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianSplitChartCoordinates

/-!
# Transporting original quotient points through ambient linear equivalences

Changing ambient coordinates transports the full relation submodule and the
actual quotient. The resulting equivalence on Grassmannian points is inverse to
transport through the inverse ambient equivalence.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
variable {R M P : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup P] [Module R P] {d : ℕ}

/-- The quotient map after changing ambient coordinates. -/
def ambientTransportQuotient (e : M ≃ₗ[R] P) (N : Module.Grassmannian R M d) :
    P →ₗ[R] (M ⧸ N.toSubmodule) := N.toSubmodule.mkQ.comp e.symm.toLinearMap

/-- Changing ambient coordinates preserves surjectivity onto the original quotient. -/
theorem ambientTransportQuotient_surjective (e : M ≃ₗ[R] P)
    (N : Module.Grassmannian R M d) : Function.Surjective (ambientTransportQuotient e N) :=
  (Submodule.mkQ_surjective _).comp e.symm.surjective

/-- The transported quotient is canonically the original quotient. -/
def ambientTransportQuotientEquiv (e : M ≃ₗ[R] P) (N : Module.Grassmannian R M d) :
    (P ⧸ (ambientTransportQuotient e N).ker) ≃ₗ[R] (M ⧸ N.toSubmodule) :=
  (ambientTransportQuotient e N).quotKerEquivOfSurjective
    (ambientTransportQuotient_surjective e N)

/-- The original relation transported to a new ambient coordinate module. -/
def ambientTransportPoint (e : M ≃ₗ[R] P) (N : Module.Grassmannian R M d) :
    Module.Grassmannian R P d where
  toSubmodule := (ambientTransportQuotient e N).ker
  finite_quotient := Module.Finite.equiv (ambientTransportQuotientEquiv e N).symm
  projective_quotient := Module.Projective.of_equiv (ambientTransportQuotientEquiv e N).symm
  rankAtStalk_eq p := by
    rw [congrFun (Module.rankAtStalk_eq_of_equiv (ambientTransportQuotientEquiv e N)) p]
    exact N.rankAtStalk_eq p

/-- Transported relation membership is exactly membership after the inverse coordinate change. -/
@[simp] theorem ambientTransportPoint_mem (e : M ≃ₗ[R] P)
    (N : Module.Grassmannian R M d) (x : P) :
    x ∈ (ambientTransportPoint e N).toSubmodule ↔ e.symm x ∈ N.toSubmodule := by
  change N.toSubmodule.mkQ (e.symm x) = 0 ↔ _
  exact Submodule.Quotient.mk_eq_zero (p := N.toSubmodule) (x := e.symm x)

/-- Transporting back recovers every original relation, not just its quotient rank. -/
@[simp] theorem ambientTransportPoint_symm (e : M ≃ₗ[R] P)
    (N : Module.Grassmannian R M d) :
    ambientTransportPoint e.symm (ambientTransportPoint e N) = N := by
  apply Module.Grassmannian.ext
  ext x
  simp only [ambientTransportPoint_mem, LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply]

/-- Ambient coordinate changes induce equivalences of the original quotient Grassmannians. -/
def ambientTransportPointEquiv (e : M ≃ₗ[R] P) :
    Module.Grassmannian R M d ≃ Module.Grassmannian R P d where
  toFun := ambientTransportPoint e
  invFun := ambientTransportPoint e.symm
  left_inv := ambientTransportPoint_symm e
  right_inv := ambientTransportPoint_symm e.symm

/-- The quotient comparison commutes with the actual quotient maps. -/
theorem ambientTransportQuotientEquiv_mkQ (e : M ≃ₗ[R] P)
    (N : Module.Grassmannian R M d) :
    (ambientTransportQuotientEquiv e N).toLinearMap.comp
      (ambientTransportPoint e N).toSubmodule.mkQ = ambientTransportQuotient e N := by
  apply LinearMap.ext
  intro x
  exact LinearMap.quotKerEquivOfSurjective_apply_mk (ambientTransportQuotient e N)
    (ambientTransportQuotient_surjective e N) x

end FLT.Mazur.GrassmannianChart
