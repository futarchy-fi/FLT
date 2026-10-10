/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXAlgebra
public import FLT.Mazur.WeierstrassSuccessiveXMonic

/-!
# The actual successive chart equals its monic presentation

Explicit inverse coordinate substitutions identify the three-generator quotient
with the monic slope algebra over the incidence base. In particular regularity
of the incidence ratio transfers to the actual chart, without eliminating u.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassSuccessiveX

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)

/-- The actual chart receives the incidence algebra by its retained coordinates. -/
def incidenceToCoordinate : SuccessiveIncidence.Coordinate π →ₐ[R]
    Coordinate W s π b3 b4 b6 :=
  SuccessiveIncidence.evaluation π (coord W s π b3 b4 b6 0) (coord W s π b3 b4 b6 2)
    (incidence W s π b3 b4 b6)

/-- The monic presentation evaluates in the actual equation chart. -/
def fromMonic : MonicCoordinate W s π b3 b4 b6 →ₐ[R] Coordinate W s π b3 b4 b6 :=
  AdjoinRoot.liftAlgHom (slopePolynomial W s π b3 b4 b6)
    (incidenceToCoordinate W s π b3 b4 b6) (coord W s π b3 b4 b6 1) (by
      rw [slopePolynomial_eval]
      simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes,
        incidenceToCoordinate, SuccessiveIncidence.evaluation_t,
        SuccessiveIncidence.evaluation_u, sub_eq_zero] using equation W s π b3 b4 b6)

/-- The monic model maps its incidence ratio to the actual ratio. -/
@[simp] theorem fromMonic_t : fromMonic W s π b3 b4 b6 (monicT W s π b3 b4 b6) =
    coord W s π b3 b4 b6 0 := by
  simp [fromMonic, monicT, AdjoinRoot.algebraMap_eq, AdjoinRoot.liftAlgHom_of,
    incidenceToCoordinate]

/-- The monic model maps its slope to the actual slope. -/
@[simp] theorem fromMonic_v : fromMonic W s π b3 b4 b6 (monicV W s π b3 b4 b6) =
    coord W s π b3 b4 b6 1 := AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The monic model preserves the retained horizontal coordinate. -/
@[simp] theorem fromMonic_u : fromMonic W s π b3 b4 b6 (monicU W s π b3 b4 b6) =
    coord W s π b3 b4 b6 2 := by
  simp [fromMonic, monicU, AdjoinRoot.algebraMap_eq, AdjoinRoot.liftAlgHom_of,
    incidenceToCoordinate]

/-- The actual three generators evaluate in the monic presentation. -/
def toMonic : Coordinate W s π b3 b4 b6 →ₐ[R] MonicCoordinate W s π b3 b4 b6 :=
  evaluation W s π b3 b4 b6
    ![monicT W s π b3 b4 b6, monicV W s π b3 b4 b6, monicU W s π b3 b4 b6]
    (monic_equation W s π b3 b4 b6) (monic_incidence W s π b3 b4 b6)

/-- Each actual generator is retained in the monic model. -/
@[simp] theorem toMonic_coord (i : Fin 3) :
    toMonic W s π b3 b4 b6 (coord W s π b3 b4 b6 i) =
      ![monicT W s π b3 b4 b6, monicV W s π b3 b4 b6, monicU W s π b3 b4 b6] i :=
  evaluation_coord _ _ _ _ _ _ _ _ _ i

/-- The monic and three-generator presentations are actual inverse algebras. -/
def monicEquiv : Coordinate W s π b3 b4 b6 ≃ₐ[R] MonicCoordinate W s π b3 b4 b6 := by
  apply AlgEquiv.ofAlgHom (toMonic W s π b3 b4 b6) (fromMonic W s π b3 b4 b6)
  · apply AdjoinRoot.algHom_ext'
    · apply SuccessiveIncidence.hom_ext
      · change toMonic W s π b3 b4 b6
          (fromMonic W s π b3 b4 b6 (monicT W s π b3 b4 b6)) = monicT W s π b3 b4 b6
        rw [fromMonic_t, toMonic_coord]
        rfl
      · change toMonic W s π b3 b4 b6
          (fromMonic W s π b3 b4 b6 (monicU W s π b3 b4 b6)) = monicU W s π b3 b4 b6
        rw [fromMonic_u, toMonic_coord]
        rfl
    · change toMonic W s π b3 b4 b6
        (fromMonic W s π b3 b4 b6 (monicV W s π b3 b4 b6)) = monicV W s π b3 b4 b6
      rw [fromMonic_v, toMonic_coord]
      rfl
  · apply hom_ext
    intro i
    change fromMonic W s π b3 b4 b6
      (toMonic W s π b3 b4 b6 (coord W s π b3 b4 b6 i)) = coord W s π b3 b4 b6 i
    rw [toMonic_coord]
    fin_cases i
    · exact fromMonic_t W s π b3 b4 b6
    · exact fromMonic_v W s π b3 b4 b6
    · exact fromMonic_u W s π b3 b4 b6

/-- The incidence ratio is regular in the actual successive equation chart. -/
theorem t_regular [IsDomain R] (hπ : π ≠ 0) : IsRegular (coord W s π b3 b4 b6 0) := by
  let e := monicEquiv W s π b3 b4 b6
  have he : e (coord W s π b3 b4 b6 0) = monicT W s π b3 b4 b6 := toMonic_coord _ _ _ _ _ _ 0
  have hr := monicT_regular W s π b3 b4 b6 hπ
  refine ⟨?_, ?_⟩
  · intro a b h
    apply e.injective
    apply hr.left
    simpa only [map_mul, he] using congrArg e h
  · intro a b h
    apply e.injective
    apply hr.right
    simpa only [map_mul, he] using congrArg e h

end FLT.Mazur.WeierstrassSuccessiveX
