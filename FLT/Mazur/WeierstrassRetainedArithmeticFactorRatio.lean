/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedNodeFactorRatioPuncture
public import FLT.Mazur.WeierstrassModificationXArithmeticFactorRatioLaurent

/-!
# The full corrected retained chart at each original arithmetic order

Integral divided coefficients define both roots on the original whole node.
The full right boundary recovers the independently constructed arithmetic ratio.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages PolygonSmoothing WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s c3 c4 c6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ c3) (h4 : π ∣ c4) (h6 : π ∣ c6)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "J" => ideal Q (parameter R π m)
local notation "d" => Classical.choose hs
local notation "hd" => Classical.choose_spec hs
local notation "τ" => arithmeticInitialMobiusSmoothing W ha s π m

/-- The full retained arithmetic node maps to the exact normalized target node. -/
def arithmeticRetainedFactorRatioChart : chart Q (parameter R π m) ⟶ chart Q τ :=
  retainedFactorRatioChart (W.map q) (q π) (q s) (q c3) (q c4) (q c6) J
    (arithmeticParameterIdeal_nilpotent π m) (ha.map q) (arithmeticCoefficient_mem π m hs)
    (arithmeticCoefficient_mem π m h2) (arithmeticCoefficient_mem π m h3)
    (arithmeticCoefficient_mem π m h4) (arithmeticCoefficient_mem π m h6) (q d)
    (by simpa only [map_mul] using congrArg q hd)

local notation "F" => arithmeticRetainedFactorRatioChart π m W s c3 c4 c6 ha hs h2 h3 h4 h6
local notation "H3" => dvd_mul_of_dvd_right h3 π
local notation "H4" => dvd_mul_of_dvd_right h4 π
local notation "H6" => dvd_mul_of_dvd_right h6 (π ^ 2)
local notation "E" => arithmeticFactorRatioLaurentIso π m W s (π * c3) (π * c4)
  (π ^ 2 * c6) ha hs h2 H3 H4 H6

/-- The complete right arithmetic boundary uses the original full corrected Laurent isomorphism. -/
@[reassoc] theorem arithmeticRetainedFactorRatioChart_right :
    rightBranchOpen Q (parameter R π m) ≫ F =
      (E).hom ≫ (edgeInversion Q).hom ≫ rightBranchOpen Q τ := by
  unfold arithmeticRetainedFactorRatioChart arithmeticFactorRatioLaurentIso
  simp only [map_mul, map_pow]
  exact retainedFactorRatioChart_right_boundary ..

variable (b3 b4 b6 : R) (hb3 : b3 = π * c3) (hb4 : b4 = π * c4)
  (hb6 : b6 = π ^ 2 * c6)

include hb3 hb4 hb6 in
/-- Independently named original coefficients have the same entire retained boundary. -/
@[reassoc] theorem arithmeticRetainedFactorRatioChart_right_of_eq
    (hB3 : π ∣ b3) (hB4 : π ∣ b4) (hB6 : π ∣ b6) :
    rightBranchOpen Q (parameter R π m) ≫ F =
      (arithmeticFactorRatioLaurentIso π m W s b3 b4 b6 ha hs h2 hB3 hB4 hB6).hom ≫
        (edgeInversion Q).hom ≫ rightBranchOpen Q τ := by
  subst b3 b4 b6
  exact arithmeticRetainedFactorRatioChart_right ..

end FLT.Mazur.WeierstrassModificationX
