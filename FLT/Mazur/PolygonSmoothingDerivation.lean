/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingRing
public import FLT.Mazur.QuotientRelativeDerivation
public import Mathlib.Algebra.MvPolynomial.Derivation

/-!
# Derivations of the actual arithmetic node chart

Derivations of the original xy=t algebra are exactly pairs of coordinate
values satisfying x dy + y dx = 0. Both the equation and its converse are
proved for the actual quotient algebra, over an arbitrary coefficient ring.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PolygonSmoothing

set_option backward.isDefEq.respectTransparency false

variable {R N : Type*} [CommRing R] (t : R) [AddCommGroup N] [Module R N]
  [Module (ChartRing t) N]

/-- Differentiating the original smoothing equation gives its actual cotangent relation. -/
theorem derivation_coordinate_relation (d : Derivation R (ChartRing t) N) :
    leftCoordinate t • d (rightCoordinate t) + rightCoordinate t • d (leftCoordinate t) = 0 := by
  rw [← d.leibniz, coordinate_relation, d.map_algebraMap]

variable [Module (MvPolynomial (Fin 2) R) N]
  [IsScalarTower R (MvPolynomial (Fin 2) R) N]
  [IsScalarTower (MvPolynomial (Fin 2) R) (ChartRing t) N]

/-- A pair satisfying the differential equation gives an actual quotient derivation. -/
def derivationOfCoordinates (u v : N)
    (huv : leftCoordinate t • v + rightCoordinate t • u = 0) :
    Derivation R (ChartRing t) N := by
  let d := MvPolynomial.mkDerivation R ![u, v]
  have hd : d (relation t) = 0 := by
    simp only [relation, map_sub, d.leibniz, MvPolynomial.derivation_C, sub_zero]
    dsimp only [d]
    rw [MvPolynomial.mkDerivation_X, MvPolynomial.mkDerivation_X]
    change (MvPolynomial.X (0 : Fin 2)) • v + (MvPolynomial.X (1 : Fin 2)) • u = 0
    rw [← algebraMap_smul (ChartRing t) (MvPolynomial.X (0 : Fin 2)),
      ← algebraMap_smul (ChartRing t) (MvPolynomial.X (1 : Fin 2))]
    exact huv
  apply QuotientRelativeDerivation.lift (relationIdeal t) d
  intro p hp
  obtain ⟨p, rfl⟩ := Ideal.mem_span_singleton'.mp hp
  rw [d.leibniz, hd, smul_zero, zero_add]
  have hz : algebraMap (MvPolynomial (Fin 2) R) (ChartRing t) (relation t) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [← algebraMap_smul (ChartRing t) (relation t), hz]
  exact zero_smul (ChartRing t) (d p)

/-- The constructed derivation has its prescribed first coordinate value. -/
@[simp] theorem derivationOfCoordinates_left (u v : N)
    (huv : leftCoordinate t • v + rightCoordinate t • u = 0) :
    derivationOfCoordinates t u v huv (leftCoordinate t) = u := by
  exact MvPolynomial.mkDerivation_X R ![u, v] 0

/-- The constructed derivation has its prescribed second coordinate value. -/
@[simp] theorem derivationOfCoordinates_right (u v : N)
    (huv : leftCoordinate t • v + rightCoordinate t • u = 0) :
    derivationOfCoordinates t u v huv (rightCoordinate t) = v := by
  exact MvPolynomial.mkDerivation_X R ![u, v] 1

omit [IsScalarTower R (MvPolynomial (Fin 2) R) N] in
/-- Two coordinate values determine a relative derivation of the actual chart. -/
theorem chartRing_derivation_ext (d e : Derivation R (ChartRing t) N)
    (hx : d (leftCoordinate t) = e (leftCoordinate t))
    (hy : d (rightCoordinate t) = e (rightCoordinate t)) : d = e := by
  have he : d.compAlgebraMap (MvPolynomial (Fin 2) R) =
      e.compAlgebraMap (MvPolynomial (Fin 2) R) := by
    apply MvPolynomial.derivation_ext
    intro i
    fin_cases i
    · exact hx
    · exact hy
  ext a : 1
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact Derivation.congr_fun he a

/-- The arithmetic relation presents all relative derivations of the actual node chart. -/
def derivationCoordinateEquiv :
    Derivation R (ChartRing t) N ≃
      {p : N × N // leftCoordinate t • p.2 + rightCoordinate t • p.1 = 0} where
  toFun d := ⟨(d (leftCoordinate t), d (rightCoordinate t)), derivation_coordinate_relation t d⟩
  invFun p := derivationOfCoordinates t p.val.1 p.val.2 p.property
  left_inv _d := chartRing_derivation_ext t _ _
    (derivationOfCoordinates_left ..) (derivationOfCoordinates_right ..)
  right_inv _p := Subtype.ext (Prod.ext
    (derivationOfCoordinates_left ..) (derivationOfCoordinates_right ..))

end FLT.Mazur.PolygonSmoothing
