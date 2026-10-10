/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginGlobalSectionUnique
public import FLT.Mazur.WeierstrassOriginAutomorphismCoordinates
public import FLT.Mazur.ModuleGlobalTransportCoefficients
public import FLT.Mazur.ModuleSectionTransportRestriction
public import FLT.Mazur.AffineImmersionSectionPullback

/-!
# Transport of actual origin-divisor sections under automorphisms

The intrinsic line pullback transports global sections and preserves the
canonical section. On the original affine chart its coefficient is the
actual coordinate pullback, even when the parameter neighborhood moves.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open FLT.Mazur.AffineImmersionSectionCoordinates
open FLT.Mazur.ModuleSheafBinarySections

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)
  (e : integralCurve W ≅ integralCurve W)
  (hz : integralCurveZero W ≫ e.hom = integralCurveZero W)

/-- The actual intrinsic line comparison, sealed before section transport. -/
@[irreducible] def originAutDivisorMap (n : ℕ) :
    (pullback e.hom).obj (originDivisorLine W n) ⟶ originDivisorLine W n :=
  (originAutDivisorLineIso W e hz n).hom

/-- The sealed comparison retains the original canonical section morphism. -/
theorem originAutDivisorMap_section (n : ℕ) :
    (pullback e.hom).map
        (FCurve.divisorSectionMap (originIdealSheaf_power_effectiveCartier W n)) ≫
        originAutDivisorMap W e hz n =
      (FCurve.modulePullbackUnitIso e.hom).hom ≫
        FCurve.divisorSectionMap (originIdealSheaf_power_effectiveCartier W n) := by
  unfold originAutDivisorMap
  exact originAutDivisorLineIso_section W e hz n

/-- The actual positive-line pullback on global sections of the original cubic. -/
def originAutDivisorTransport (n : ℕ) :
    Γ(originDivisorLine W n, ⊤) → Γ(originDivisorLine W n, ⊤) :=
  FCurve.globalSectionTransport e.hom (originAutDivisorMap W e hz n)

/-- Transport preserves the actual global canonical divisor section. -/
theorem originAutDivisorTransport_canonical (n : ℕ) :
    originAutDivisorTransport W e hz n
        (FCurve.divisorSection (originIdealSheaf_power_effectiveCartier W n) ⊤) =
      FCurve.divisorSection (originIdealSheaf_power_effectiveCartier W n) ⊤ :=
  FCurve.globalSectionTransport_section e.hom (originAutDivisorMap W e hz n)
    (FCurve.divisorSectionMap (originIdealSheaf_power_effectiveCartier W n))
    (FCurve.divisorSectionMap (originIdealSheaf_power_effectiveCartier W n))
    (originAutDivisorMap_section W e hz n)

variable (hΔ : IsUnit W.Δ)
  (hb : e.hom ≫ integralCurveStructure W = integralCurveStructure W)

/-- The affine restriction of transport has exactly the original pulled-back coefficient. -/
theorem originAutDivisorTransport_affine (n : ℕ) (a : Coordinate W 2)
    (s : Γ(originDivisorLine W n, ⊤))
    (hs : res (originDivisorLine W n) le_top s = originAffinePoleSection W n a) :
    res (originDivisorLine W n) le_top (originAutDivisorTransport W e hz n s) =
      originAffinePoleSection W n (originAutCoordinateHom W hΔ e hb hz a) := by
  let j := integralCurveChart W 2
  let σ := (originAutCoordinateHom W hΔ e hb hz).toRingHom
  have hsq : Spec.map (CommRingCat.ofHom σ) ≫ j = j ≫ e.hom := by
    rw [originAutCoordinateHom_spec]
    exact originAutAffineHom_inclusion W hΔ e hb hz
  let hU := image_le_preimage j j e.hom σ hsq
  let r := (coordinates j).symm a
  have hcan : (originDivisorLine W n).presheaf.map
      (homOfLE (show (originAffineOpen W).1 ≤ ⊤ from le_top)).op
        (FCurve.divisorSection (originIdealSheaf_power_effectiveCartier W n) ⊤) =
      FCurve.divisorSection (originIdealSheaf_power_effectiveCartier W n) (originAffineOpen W).1 :=
    FCurve.divisorSection_restrict (originIdealSheaf_power_effectiveCartier W n) le_top
  have hs' : (originDivisorLine W n).presheaf.map
      (homOfLE (show (originAffineOpen W).1 ≤ ⊤ from le_top)).op s =
      r • (originDivisorLine W n).presheaf.map
        (homOfLE (show (originAffineOpen W).1 ≤ ⊤ from le_top)).op
          (FCurve.divisorSection (originIdealSheaf_power_effectiveCartier W n) ⊤) := by
    rw [hcan]
    exact hs
  have ht := FCurve.globalSectionTransport_coefficient e.hom
    (originAutDivisorMap W e hz n)
    (FCurve.divisorSection (originIdealSheaf_power_effectiveCartier W n) ⊤) s
    (FCurve.divisorSection (originIdealSheaf_power_effectiveCartier W n) ⊤)
    (originAutDivisorTransport_canonical W e hz n)
    (originAffineOpen W).1 (originAffineOpen W).1 hU r hs'
  have hr : e.hom.appLE (originAffineOpen W).1 (originAffineOpen W).1 hU r =
      (coordinates j).symm (σ a) := by
    apply (coordinates j).injective
    rw [coordinates_pullback j j e.hom σ hsq, RingEquiv.apply_symm_apply]
    exact ((coordinates j).apply_symm_apply (σ a)).symm
  rw [hr, hcan] at ht
  exact ht

end FLT.Mazur.WeierstrassIntegralChart
