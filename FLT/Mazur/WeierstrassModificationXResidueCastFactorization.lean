/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXResidueGeneratorReduction

/-!
# Exact coefficient-cast factorization of the original residue comparison

The source of the cast is kept as `ExtendedCoordinate`, matching the original
construction before any coordinate evaluation. The original depth conditions
supply all three vanishing coefficients. The final factor is the existing full
normal-form equivalence, with the constant-depth coefficient retained.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace FLT.Mazur.WeierstrassModificationX

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Transport the coefficient-extended chart after its three coefficients vanish. -/
def zeroExtendedCoefficientsEquiv {R S B : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [CommRing B] [Algebra S B] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
    (hs : algebraMap R S s = 0) (h3 : algebraMap R S b3 = 0)
    (h4 : algebraMap R S b4 = 0)
    (e : Coordinate (W.map (algebraMap R S)) 0 0 0 (algebraMap R S b6) ≃ₐ[S] B) :
    ExtendedCoordinate W s b3 b4 b6 S ≃ₐ[S] B := by
  change Coordinate _ _ _ _ _ ≃ₐ[_] _
  rw [hs, h3, h4]
  exact e

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * k ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)

local notation "K" => ResidueField R
local notation "W'" => W.map (algebraMap R K)
local notation "c" => algebraMap R K b6

/-- The existing residue comparison is exactly this cast of the full normal-form map. -/
theorem residueCoordinateEquiv_eq_cast : residueCoordinateEquiv D k hk0 hk b3 b4 b6 h3 h4 =
    zeroExtendedCoefficientsEquiv W (π ^ k) b3 b4 b6
      (show algebraMap R K (π ^ k) = 0 from
        WeierstrassDilatation.residue_scale_eq_zero D k hk0)
      (show algebraMap R K b3 = 0 from (residue_eq_zero_iff _).mpr
        (WeierstrassDilatation.divided_linear_mem D k hk b3 b4 h3 h4).1)
      (show algebraMap R K b4 = 0 from (residue_eq_zero_iff _).mpr
        (WeierstrassDilatation.divided_linear_mem D k hk b3 b4 h3 h4).2)
      (fiberNormalEquiv (residue R W.a₁) c W' rfl ((residue_eq_zero_iff _).mpr D.a₂_mem)) := rfl

/-- The sealed original comparison has the same precise coefficient-cast factorization. -/
theorem residueCoordinateSealedEquiv_eq_cast :
    residueCoordinateSealedEquiv D k hk0 hk b3 b4 b6 h3 h4 =
    zeroExtendedCoefficientsEquiv W (π ^ k) b3 b4 b6
      (show algebraMap R K (π ^ k) = 0 from
        WeierstrassDilatation.residue_scale_eq_zero D k hk0)
      (show algebraMap R K b3 = 0 from (residue_eq_zero_iff _).mpr
        (WeierstrassDilatation.divided_linear_mem D k hk b3 b4 h3 h4).1)
      (show algebraMap R K b4 = 0 from (residue_eq_zero_iff _).mpr
        (WeierstrassDilatation.divided_linear_mem D k hk b3 b4 h3 h4).2)
      (fiberNormalEquiv (residue R W.a₁) c W' rfl ((residue_eq_zero_iff _).mpr D.a₂_mem)) :=
  (residueCoordinateSealedEquiv_def D k hk0 hk b3 b4 b6 h3 h4).trans
    (residueCoordinateEquiv_eq_cast D k hk0 hk b3 b4 b6 h3 h4)

end FLT.Mazur.WeierstrassModificationX
