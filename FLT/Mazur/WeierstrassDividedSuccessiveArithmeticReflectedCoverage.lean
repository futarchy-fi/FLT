/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSuccessiveTensorReflectedAddition
public import FLT.Mazur.WeierstrassDividedNodalReflectedPuncturedCover
public import FLT.Mazur.WeierstrassSuccessiveXArithmeticPuncturedBranches

/-!
# Reflected coverage of punctured arithmetic tensor pairs

The original two horizontal coordinates and arithmetic nilpotence imply
membership in one of three constructed smooth-output domains. Branch choices
and secant denominators are consequences, rather than extra input premises.
-/

@[expose] public noncomputable section
open AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX PolygonArithmeticStages
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {k l n depth : ℕ}
  (D : SplitNodeDepth W π depth)
  (d : Data W π k) (d' : Data W π (k + 1)) (e : Data W π l) (e' : Data W π (l + 1))
  (m : ℕ) (hkl : k ≤ l) (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (j : ℕ) (hj : j ≤ n) (hstage : depth - k - l ≤ j)
  (hl : 2 * l < depth) (hm : depth ≤ k + 2 * l)
local notation "hπ" => D.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "P" => SuccessiveTensorPairRing d' e' Q
local notation "f" => successiveTensorPairInput hπ d d' e e' Q
local notation "u₁" => successiveTensorPairLeft d' e' Q
  (tensorCoord W (π ^ k) π d'.b3 d'.b4 d'.b6 Q 2)
local notation "u₂" => successiveTensorPairRight d' e' Q
  (tensorCoord W (π ^ l) π e'.b3 e'.b4 e'.b6 Q 2)
local notation "V₊" => successiveTensorReflectedPositiveOpen D d d' e e' Q hkl data
  j hj hstage hl.le hm
local notation "V₋" => successiveTensorReflectedNegativeOpen D d d' e e' Q hkl data
  j hj hstage hl.le hm
local notation "V₀" =>
  successiveTensorReflectedOppositeOpen D d d' e e' Q hkl data j hj hstage hl.le

/-- Every actual punctured arithmetic pair has a constructed smooth resolved output domain. -/
theorem successiveArithmeticReflected_punctured_cover (hk : 0 < k) (hlt : k < l)
    (p : PrimeSpectrum P)
    (hx : u₁ ∉ p.asIdeal) (hu : u₂ ∉ p.asIdeal) :
    p ∈ V₊ ∨ p ∈ V₋ ∨ p ∈ V₀ := by
  let q := PrimeSpectrum.comap (f).toRingHom p
  have hp : algebraMap R (UnequalPairRing d e) π ∈ q.asIdeal := by
    change f (algebraMap R (UnequalPairRing d e) π) ∈ p.asIdeal
    rw [AlgHom.commutes]
    exact arithmeticPrime_parameter_mem π m P p
  have hx' : unequalPairLeft d e
      (WeierstrassDilatation.x W (π ^ k) d.b3 d.b4 d.b6) ∉ q.asIdeal := by
    change f (unequalPairLeft d e _) ∉ p.asIdeal
    rwa [successiveTensorPairInput_left_apply, successiveTensorInput_x]
  have hu' : unequalPairRight d e
      (WeierstrassDilatation.x W (π ^ l) e.b3 e.b4 e.b6) ∉ q.asIdeal := by
    change f (unequalPairRight d e _) ∉ p.asIdeal
    rwa [successiveTensorPairInput_right_apply, successiveTensorInput_x]
  exact nodalReflectedPuncturedUnequal_cover D d e hkl data (hstage.trans hj) hl hm
    (unequalPairLeft d e) (unequalPairRight d e) hk hlt q hp hx' hu'

/-- The full horizontal puncture is covered by the three actual addition opens. -/
theorem successiveArithmeticReflected_punctured_le (hk : 0 < k) (hlt : k < l) :
    PrimeSpectrum.basicOpen u₁ ⊓ PrimeSpectrum.basicOpen u₂ ≤ V₊ ⊔ (V₋ ⊔ V₀) := by
  intro p hp
  exact successiveArithmeticReflected_punctured_cover D d d' e e' m hkl data
    j hj hstage hl hm hk hlt p hp.1 hp.2

end FLT.Mazur.WeierstrassDividedDepth
