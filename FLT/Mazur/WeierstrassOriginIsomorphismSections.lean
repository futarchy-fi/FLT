/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginIsomorphismDivisor
public import FLT.Mazur.WeierstrassOriginIsomorphismCoordinates
public import FLT.Mazur.WeierstrassOriginAutomorphismSections

/-!
# Transport of origin-divisor sections between distinct cubics

The intrinsic pullback transports actual global divisor sections. Its affine
coefficient is the recovered coordinate pullback of the original isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open FLT.Mazur.AffineImmersionSectionCoordinates FLT.Mazur.ModuleSheafBinarySections

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (W V : WeierstrassCurve R)
  (e : integralCurve W ≅ integralCurve V)
  (hz : integralCurveZero W ≫ e.hom = integralCurveZero V)

/-- The actual line comparison, sealed before transporting its sections. -/
@[irreducible] def originIsoDivisorMap (n : ℕ) :
    (pullback e.hom).obj (originDivisorLine V n) ⟶ originDivisorLine W n :=
  (originIsoDivisorLineIso W V e hz n).hom

/-- The sealed comparison retains the canonical section morphism. -/
theorem originIsoDivisorMap_section (n : ℕ) :
    (pullback e.hom).map
        (FCurve.divisorSectionMap (originIdealSheaf_power_effectiveCartier V n)) ≫
        originIsoDivisorMap W V e hz n =
      (FCurve.modulePullbackUnitIso e.hom).hom ≫
        FCurve.divisorSectionMap (originIdealSheaf_power_effectiveCartier W n) := by
  unfold originIsoDivisorMap
  exact originIsoDivisorLineIso_section W V e hz n

/-- Pull back actual global positive-divisor sections from target to source. -/
def originIsoDivisorTransport (n : ℕ) :
    Γ(originDivisorLine V n, ⊤) → Γ(originDivisorLine W n, ⊤) :=
  FCurve.globalSectionTransport e.hom (originIsoDivisorMap W V e hz n)

/-- The target canonical section pulls back to the source canonical section. -/
theorem originIsoDivisorTransport_canonical (n : ℕ) :
    originIsoDivisorTransport W V e hz n
        (FCurve.divisorSection (originIdealSheaf_power_effectiveCartier V n) ⊤) =
      FCurve.divisorSection (originIdealSheaf_power_effectiveCartier W n) ⊤ :=
  FCurve.globalSectionTransport_section e.hom (originIsoDivisorMap W V e hz n)
    (FCurve.divisorSectionMap (originIdealSheaf_power_effectiveCartier V n))
    (FCurve.divisorSectionMap (originIdealSheaf_power_effectiveCartier W n))
    (originIsoDivisorMap_section W V e hz n)

variable (hV : IsUnit V.Δ)
  (hb : e.hom ≫ integralCurveStructure V = integralCurveStructure W)

/-- The transported section has exactly the coefficient supplied by the scheme isomorphism. -/
theorem originIsoDivisorTransport_affine (n : ℕ) (a : Coordinate V 2)
    (s : Γ(originDivisorLine V n, ⊤))
    (hs : res (originDivisorLine V n) le_top s = originAffinePoleSection V n a) :
    res (originDivisorLine W n) le_top (originIsoDivisorTransport W V e hz n s) =
      originAffinePoleSection W n (originIsoCoordinateHom W V hV e hb hz a) := by
  let j := integralCurveChart V 2
  let k := integralCurveChart W 2
  let σ := (originIsoCoordinateHom W V hV e hb hz).toRingHom
  have hsq : Spec.map (CommRingCat.ofHom σ) ≫ j = k ≫ e.hom := by
    rw [originIsoCoordinateHom_spec]
    exact originIsoAffineHom_inclusion W V hV e hb hz
  let hU := image_le_preimage j k e.hom σ hsq
  let r := (coordinates j).symm a
  have hcan (A : WeierstrassCurve R) : (originDivisorLine A n).presheaf.map
      (homOfLE (show (originAffineOpen A).1 ≤ ⊤ from le_top)).op
        (FCurve.divisorSection (originIdealSheaf_power_effectiveCartier A n) ⊤) =
      FCurve.divisorSection (originIdealSheaf_power_effectiveCartier A n)
        (originAffineOpen A).1 :=
    FCurve.divisorSection_restrict (originIdealSheaf_power_effectiveCartier A n) le_top
  have hs' : (originDivisorLine V n).presheaf.map
      (homOfLE (show (originAffineOpen V).1 ≤ ⊤ from le_top)).op s =
      r • (originDivisorLine V n).presheaf.map
        (homOfLE (show (originAffineOpen V).1 ≤ ⊤ from le_top)).op
          (FCurve.divisorSection (originIdealSheaf_power_effectiveCartier V n) ⊤) := by
    rw [hcan V]
    exact hs
  have ht := FCurve.globalSectionTransport_coefficient e.hom
    (originIsoDivisorMap W V e hz n)
    (FCurve.divisorSection (originIdealSheaf_power_effectiveCartier V n) ⊤) s
    (FCurve.divisorSection (originIdealSheaf_power_effectiveCartier W n) ⊤)
    (originIsoDivisorTransport_canonical W V e hz n)
    (originAffineOpen V).1 (originAffineOpen W).1 hU r hs'
  have hr : e.hom.appLE (originAffineOpen V).1 (originAffineOpen W).1 hU r =
      (coordinates k).symm (σ a) := by
    apply (coordinates k).injective
    rw [coordinates_pullback j k e.hom σ hsq, RingEquiv.apply_symm_apply]
    exact ((coordinates k).apply_symm_apply (σ a)).symm
  rw [hr, hcan W] at ht
  exact ht

end FLT.Mazur.WeierstrassIntegralChart
