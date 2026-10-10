/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationBaseChange
public import FLT.Mazur.WeierstrassDilatationFiberNormalForm
public import FLT.Mazur.WeierstrassDilatationResidueDepth

/-!
# The actual residue fiber of every bounded split-depth chart

The tensor product over the residue field is identified with the tangent
product equation. The coefficients vanish by the original split-depth
hypotheses. No fiber model or comparison is supplied as an assumption.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace FLT.Mazur.WeierstrassDilatation

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * k ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)

/-- The residue of a₁ is a specified unit coming from the original split equation. -/
def residueTangentUnit : (ResidueField R)ˣ := (D.a₁_unit.map (residue R)).unit

omit [IsDomain R] in
/-- The chosen unit retains the actual original tangent coefficient. -/
theorem residueTangentUnit_val : (↑(residueTangentUnit D) : ResidueField R) =
    residue R W.a₁ := (D.a₁_unit.map (residue R)).unit_spec

/-- The actual coefficient-specialized algebra has the tangent product normal form. -/
def residueCoordinateEquiv :
    ExtendedCoordinate W (π ^ k) b3 b4 b6 (ResidueField R) ≃ₐ[ResidueField R]
      NodalFiber.Coordinate (residue R b6) := by
  obtain ⟨hb3, hb4⟩ := divided_linear_mem D k hk b3 b4 h3 h4
  have hs : algebraMap R (ResidueField R) (π ^ k) = 0 :=
    residue_scale_eq_zero D k hk0
  have h2 : (W.map (algebraMap R (ResidueField R))).a₂ = 0 :=
    (residue_eq_zero_iff _).mpr D.a₂_mem
  have h1 : (W.map (algebraMap R (ResidueField R))).a₁ = residueTangentUnit D :=
    (residueTangentUnit_val D).symm
  have h3' : algebraMap R (ResidueField R) b3 = 0 := (residue_eq_zero_iff _).mpr hb3
  have h4' : algebraMap R (ResidueField R) b4 = 0 := (residue_eq_zero_iff _).mpr hb4
  change Coordinate _ _ _ _ _ ≃ₐ[_] _
  rw [hs, h3', h4']
  exact fiberTangentEquiv _ (residueTangentUnit D) _ h1 h2

/-- The tensor residue fiber of the original integral chart is the actual equation pq = c. -/
def residueFiberEquiv :
    ScalarExtension W (π ^ k) b3 b4 b6 (ResidueField R) ≃ₐ[ResidueField R]
      NodalFiber.Coordinate (residue R b6) :=
  (baseChangeEquiv W (π ^ k) b3 b4 b6 (ResidueField R)).trans
    (residueCoordinateEquiv D k hk0 hk b3 b4 b6 h3 h4)

variable (h6 : W.a₆ = (π ^ k) ^ 2 * b6)

/-- Before the middle depth this same tensor fiber is the product-zero node. -/
def residueNodeEquiv (hstrict : 2 * k < n) :
    ScalarExtension W (π ^ k) b3 b4 b6 (ResidueField R) ≃ₐ[ResidueField R]
      NodalFiber.Coordinate (0 : ResidueField R) := by
  have hc : residue R b6 = 0 :=
    (residue_eq_zero_iff _).mpr (divided_constant_mem D k hstrict b6 h6)
  exact (residueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4).trans
    (by rw [hc])

omit [IsDomain R] in
include D h6 in
/-- At the middle depth both tangent factors are units on the whole residue fiber. -/
theorem middle_tangent_units (hmiddle : 2 * k = n) :
    IsUnit (NodalFiber.p (residue R b6)) ∧ IsUnit (NodalFiber.q (residue R b6)) := by
  have hc := ((divided_constant_isUnit D k hmiddle b6 h6).map (residue R)).map
    (algebraMap (ResidueField R) (NodalFiber.Coordinate (residue R b6)))
  rw [← NodalFiber.relation] at hc
  exact ⟨isUnit_of_mul_isUnit_left hc, isUnit_of_mul_isUnit_right hc⟩

end FLT.Mazur.WeierstrassDilatation
