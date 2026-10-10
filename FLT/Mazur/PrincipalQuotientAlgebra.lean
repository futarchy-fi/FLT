/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalQuotientArrow

/-!
# Algebra maps between canonical principal quotients

The canonical projection and the maps obtained from inverse-coordinate
relations preserve the original base algebra structures.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PrincipalQuotientProjection

universe u v w

variable (R : Type u) [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P) (r : P)

/-- Canonical principal quotient projection as an algebra homomorphism. -/
def projectionAlgHom : Localization.Away r →ₐ[R] Target I r where
  __ := projection I r
  commutes' x := by
    change projection I r (algebraMap R (Localization.Away r) x) =
      algebraMap R (Target I r) x
    rw [IsScalarTower.algebraMap_apply R P (Localization.Away r), projection_algebraMap]
    exact (IsScalarTower.algebraMap_apply R (P ⧸ I) (Target I r) x).symm

/-- The algebra projection has the same underlying ring map. -/
theorem projectionAlgHom_toRingHom :
    (projectionAlgHom R I r).toRingHom = projection I r := rfl

variable {Q : Type w} [CommRing Q] [Algebra R Q] (J : Ideal Q) (a : Q)
  (f : Q →ₐ[R] Localization.Away r)
  (hf : J ≤ (I.map (algebraMap P (Localization.Away r))).comap f.toRingHom)
  (v : Localization.Away r)
  (hv : f a * v - 1 ∈ I.map (algebraMap P (Localization.Away r)))

/-- Inverse-coordinate relations construct an arrow over the unchanged original base ring. -/
def principalArrowAlgHom : Target J a →ₐ[R] Target I r where
  __ := principalArrow I r J a f.toRingHom hf v hv
  commutes' x := by
    rw [IsScalarTower.algebraMap_apply R (Q ⧸ J) (Target J a)]
    change principalArrow I r J a f.toRingHom hf v hv
      (algebraMap (Q ⧸ J) (Target J a) (Ideal.Quotient.mk J (algebraMap R Q x))) = _
    rw [principalArrow_numerator]
    change projection I r (f (algebraMap R Q x)) = _
    rw [f.commutes]
    exact (projectionAlgHom R I r).commutes x

/-- Algebra arrows retain the full ambient numerator equation. -/
@[simp] theorem principalArrowAlgHom_numerator (x : Q) :
    principalArrowAlgHom R I r J a f hf v hv
      (algebraMap (Q ⧸ J) (Target J a) (Ideal.Quotient.mk J x)) =
      projection I r (f x) :=
  principalArrow_numerator I r J a f.toRingHom hf v hv x

end FLT.Mazur.PrincipalQuotientProjection
