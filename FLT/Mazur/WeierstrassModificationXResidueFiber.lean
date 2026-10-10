/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXBaseChange
public import FLT.Mazur.WeierstrassModificationXFiberNormalForm
public import FLT.Mazur.WeierstrassDilatationResidueDepth

/-!
# Actual horizontal residue fibers at bounded split depth

The tensor residue fiber is the full equation t*(v*(v+a₁)-c*t²)=0.
The original depth hypotheses force c=0 before the middle depth and make c
invertible at the middle depth. These statements concern the original
horizontal chart, including all of its exceptional points.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace FLT.Mazur.WeierstrassModificationX

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * k ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)

/-- The actual specialized horizontal equation has the full split fiber normal form. -/
def residueCoordinateEquiv :
    ExtendedCoordinate W (π ^ k) b3 b4 b6 (ResidueField R) ≃ₐ[ResidueField R]
      FiberCoordinate (residue R W.a₁) (residue R b6) := by
  obtain ⟨hb3, hb4⟩ := WeierstrassDilatation.divided_linear_mem D k hk b3 b4 h3 h4
  have hs : algebraMap R (ResidueField R) (π ^ k) = 0 :=
    WeierstrassDilatation.residue_scale_eq_zero D k hk0
  have h2 : (W.map (algebraMap R (ResidueField R))).a₂ = 0 :=
    (residue_eq_zero_iff _).mpr D.a₂_mem
  have h3' : algebraMap R (ResidueField R) b3 = 0 := (residue_eq_zero_iff _).mpr hb3
  have h4' : algebraMap R (ResidueField R) b4 = 0 := (residue_eq_zero_iff _).mpr hb4
  change Coordinate _ _ _ _ _ ≃ₐ[_] _
  rw [hs, h3', h4']
  exact fiberNormalEquiv _ _ _ rfl h2

/-- The original horizontal tensor residue fiber has the full normal form. -/
def residueFiberEquiv :
    ScalarExtension W (π ^ k) b3 b4 b6 (ResidueField R) ≃ₐ[ResidueField R]
      FiberCoordinate (residue R W.a₁) (residue R b6) :=
  (baseChangeEquiv W (π ^ k) b3 b4 b6 (ResidueField R)).trans
    (residueCoordinateEquiv D k hk0 hk b3 b4 b6 h3 h4)

variable (h6 : W.a₆ = (π ^ k) ^ 2 * b6)

/-- Before the middle depth the actual tensor fiber is the three-line equation. -/
def residueLinesEquiv (hstrict : 2 * k < n) :
    ScalarExtension W (π ^ k) b3 b4 b6 (ResidueField R) ≃ₐ[ResidueField R]
      FiberCoordinate (residue R W.a₁) 0 := by
  have hc : residue R b6 = 0 := (residue_eq_zero_iff _).mpr
    (WeierstrassDilatation.divided_constant_mem D k hstrict b6 h6)
  exact (residueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4).trans (by rw [hc])

omit [IsDomain R] in
include D in
/-- The original two tangent slopes remain separated by a residue unit. -/
theorem residue_tangent_isUnit : IsUnit (residue R W.a₁) := D.a₁_unit.map (residue R)

omit [IsDomain R] in
include D h6 in
/-- At the middle depth the quadratic term remains a unit coefficient in the actual fiber. -/
theorem residue_middle_constant_isUnit (hmiddle : 2 * k = n) : IsUnit (residue R b6) :=
  (WeierstrassDilatation.divided_constant_isUnit D k hmiddle b6 h6).map (residue R)

end FLT.Mazur.WeierstrassModificationX
