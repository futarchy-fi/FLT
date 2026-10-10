/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IteratedQuotientArrow

/-!
# Algebra arrows into canonical iterated principal quotients

The arrows obtained from inverse-coordinate relations preserve the original
base algebra structure at both localization levels.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.IteratedQuotientProjection

universe u v w

variable (R : Type u) [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P) (r : P) (s : Localization.Away r)

variable {Q : Type w} [CommRing Q] [Algebra R Q] (J : Ideal Q) (a : Q)
  (f : Q →ₐ[R] Localization.Away s)
  (hf : J ≤ ((I.map (algebraMap P (Localization.Away r))).map
    (algebraMap _ (Localization.Away s))).comap f.toRingHom)
  (v : Localization.Away s)
  (hv : f a * v - 1 ∈ (I.map (algebraMap P (Localization.Away r))).map
    (algebraMap _ (Localization.Away s)))

/-- Inverse-coordinate relations construct an arrow over the unchanged original base ring. -/
def principalArrowAlgHom : PrincipalQuotientProjection.Target J a →ₐ[R] Target I r s where
  __ := principalArrow I r s J a f.toRingHom hf v hv
  commutes' x := by
    rw [IsScalarTower.algebraMap_apply R (Q ⧸ J) (PrincipalQuotientProjection.Target J a)]
    change principalArrow I r s J a f.toRingHom hf v hv
      (algebraMap (Q ⧸ J) (PrincipalQuotientProjection.Target J a)
        (Ideal.Quotient.mk J (algebraMap R Q x))) = _
    rw [principalArrow_numerator]
    change projection I r s (f (algebraMap R Q x)) = _
    rw [f.commutes]
    exact (projectionAlgHom I r s R).commutes x

/-- Algebra arrows retain the full ambient numerator equation. -/
@[simp] theorem principalArrowAlgHom_numerator (x : Q) :
    principalArrowAlgHom R I r s J a f hf v hv
      (algebraMap (Q ⧸ J) (PrincipalQuotientProjection.Target J a) (Ideal.Quotient.mk J x)) =
      projection I r s (f x) :=
  principalArrow_numerator I r s J a f.toRingHom hf v hv x

end FLT.Mazur.IteratedQuotientProjection
