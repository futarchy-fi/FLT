/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSuccessiveTensorPairAddition
public import FLT.Mazur.WeierstrassDividedUnequalDepthZeroNodalCoverage
public import FLT.Mazur.WeierstrassDividedUnequalDepthZeroMiddleCoverage
public import FLT.Mazur.WeierstrassSuccessiveXArithmeticPuncturedBranches

/-!
# Full tensor coverage for zero-depth and positive-depth inputs

The unequal-depth output covers both punctured inputs up to the middle depth.
The flat integral pair supplies the formula before pullback to the original
arithmetic quotient, so no flatness is assumed of that quotient.
-/

@[expose] public noncomputable section
open AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation WeierstrassSuccessiveX PolygonArithmeticStages
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {k l n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (d : Data W π k) (d' : Data W π (k + 1))
  (e : Data W π l) (e' : Data W π (l + 1)) (hkl : k ≤ l)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (j : ℕ) (hj : j ≤ n) (hsum : k + l ≤ j) (m : ℕ)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "T" => SuccessiveTensorPairRing d' e' Q
local notation "g" => successiveTensorPairInput hπ d d' e e' Q
local notation "a" => unequalPairLeft d e
local notation "b" => unequalPairRight d e
local notation "u₁" => successiveTensorPairLeft d' e' Q
  (tensorCoord W (π ^ k) π d'.b3 d'.b4 d'.b6 Q 2)
local notation "u₂" => successiveTensorPairRight d' e' Q
  (tensorCoord W (π ^ l) π e'.b3 e'.b4 e'.b6 Q 2)

/-- Every punctured zero/positive pair up to the middle has its actual unequal-depth output. -/
theorem successiveTensorPairOpposite_zero_le_middle_mem
    (hk : k = 0) (hl : 0 < l) (hd : 2 * l ≤ depth)
    (p : PrimeSpectrum T) (hx : u₁ ∉ p.asIdeal) (hu : u₂ ∉ p.asIdeal) :
    p ∈ successiveTensorPairOppositeOpen hπ d d' e e' Q hkl data j hj hsum := by
  let q := PrimeSpectrum.comap (g).toRingHom p
  have hp : algebraMap R (UnequalPairRing d e) π ∈ q.asIdeal := by
    change g (algebraMap R (UnequalPairRing d e) π) ∈ p.asIdeal
    rw [AlgHom.commutes]
    exact arithmeticPrime_parameter_mem π m T p
  have hx' : a (x W (π ^ k) d.b3 d.b4 d.b6) ∉ q.asIdeal := by
    change g (a _) ∉ p.asIdeal
    rwa [successiveTensorPairInput_left_apply, successiveTensorInput_x]
  have hu' : b (x W (π ^ l) e.b3 e.b4 e.b6) ∉ q.asIdeal := by
    change g (b _) ∉ p.asIdeal
    rwa [successiveTensorPairInput_right_apply, successiveTensorInput_x]
  rcases lt_or_eq_of_le hd with hd | hd
  · exact unequalDepthDomain_zero_nodal_mem node d e hkl data (by omega)
      a b hk hl hd q hp hx' hu'
  · exact unequalDepthDomain_zero_middle_mem node d e hkl data (by omega)
      a b hk hl hd q hp hx'

end FLT.Mazur.WeierstrassDividedDepth
