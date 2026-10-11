/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassFractionActionGlobalComparison
public import FLT.Mazur.WeierstrassSecantHorizontalResidueAction

/-!
# The secant horizontal refinement carries the actual global action

Both integral refinement projections and the original horizontal fraction
inclusion occur in the comparison. Arbitrary specialization is then obtained
by naturality of the global action, after the integral equality is proved.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassGlobalModification WeierstrassModificationReesCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (π : R) (k : ℕ) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6) (hπ : π ≠ 0)
  (a c : Coordinate W 2 →ₐ[R] S)
  (p : Spec (.of S) ⟶ (integralSmoothOpen W).toScheme)
  (ha : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ integralCurveChart W 2 =
    p ≫ (integralSmoothOpen W).ι)
  (hp : p ≫ integralSmoothStructure W =
    (Spec.map (CommRingCat.ofHom c.toRingHom) ≫ integralCurveChart W 2) ≫
      integralCurveStructure W)
  (ψ : BlowupFractionChart.chart (modificationChartCenter W (π ^ k) 2)
    (coord W 2 0) →+* S)
  (hc : c.toRingHom = ψ.comp (algebraMap (Coordinate W 2)
    (BlowupFractionChart.chart (modificationChartCenter W (π ^ k) 2) (coord W 2 0))))
  (hflat : RingHom.Flat ψ)
local notation "T" => SecantPairRing W a c
local notation "α" => AlgHom.toRingHom
  (AlgHom.comp (secantPairPresentation W a c) (ordinaryChartAddition W false))
local notation "β" => AlgHom.toRingHom (AlgHom.comp (IsScalarTower.toAlgHom R S T) c)
local notation "p'" => Spec.map (CommRingCat.ofHom (algebraMap S T)) ≫ p
local notation "hp'" => secantPairSmooth_structure W a c p hp
local notation "hα" => secantPairSmooth_addition W a c p ha hp
local notation "ψ'" => secantHorizontalInput W (π ^ k) a c ψ
local notation "x" => coord W 2 0
local notation "hx" => centerGenerators_mem W (π ^ k) 1
local notation "hβ" => secantHorizontal_beta W π a c ψ hc
local notation "h6'" => Eq.trans h6
  (Eq.trans (congrArg (· * b6) (pow_two (π ^ k))) (mul_assoc (π ^ k) (π ^ k) b6))
local notation "hf'" => secantHorizontalInput_flat W (π ^ k) a c ψ hflat
local notation "O" => LeftSmoothFractionActionOpen W (π ^ k) b3 b4 (π ^ k * b6)
  h3 h4 h6' p' α β hp' hα x hx ψ' hβ 1
local notation "M" => secantHorizontalActionLift W π b3 b4 (π ^ k * b6)
  h3 h4 h6' a c p ha hp ψ hc hflat
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap T O)) ≫
  Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "j" => originalFractionCoverMap W (π ^ k) b3 b4 b6
  h3 h4 h6 (pow_ne_zero k hπ) (some 1)
local notation "b" => Spec.map (CommRingCat.ofHom ψ) ≫ j
local notation "act" => smoothPointAction W (π ^ k) b3 b4 b6 h3 h4 h6 (pow_ne_zero k hπ)

/-- The two retained secant and quotient refinements preserve the common coefficient point. -/
theorem secantHorizontalGlobalInput_structure :
    (q ≫ p) ≫ integralSmoothStructure W = (q ≫ b) ≫
      structureMap W (π ^ k) b3 b4 b6 h3 h4 h6 (pow_ne_zero k hπ) := by
  have h := fractionActionGlobalInput_structure W (π ^ k) b3 b4 b6
    h3 h4 h6 (pow_ne_zero k hπ) p c.toRingHom hp x hx ψ hc
  have h' := congrArg (q ≫ ·) h
  dsimp only [originalFractionCoverMap, centerGenerators] at h' ⊢
  simp only [Category.assoc] at h' ⊢
  convert h' using 1
  rfl

local notation "hb" => secantHorizontalGlobalInput_structure W π k b3 b4 b6
  h3 h4 h6 hπ a c p ha hp ψ hc

/-- The original secant horizontal lift is precisely the actual global modified action. -/
theorem secantHorizontalActionLift_global :
    Spec.map (CommRingCat.ofHom M) ≫ j = act (q ≫ p) (q ≫ b) hb := by
  have h := leftSmoothFractionActionLift_global W (π ^ k) b3 b4 b6
    h3 h4 h6 (pow_ne_zero k hπ) p' α β hp' hα x hx ψ' hβ hf' 1
  dsimp only [originalFractionCoverMap, centerGenerators] at h ⊢
  simp only [secantHorizontalActionLift, leftSmoothFractionActionCover_map,
    secantHorizontalInput, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc] at h ⊢
  convert h using 1
  rfl

/-- Residue specialization of the integral comparison needs no flatness of the residue map. -/
theorem secantHorizontalActionLift_global_specialize {U : Scheme.{u}}
    (e : U ⟶ Spec (.of O)) :
    e ≫ Spec.map (CommRingCat.ofHom M) ≫ j =
      act (e ≫ q ≫ p) (e ≫ q ≫ b) (by simpa only [Category.assoc] using congrArg (e ≫ ·) hb) := by
  have h := congrArg (e ≫ ·) (secantHorizontalActionLift_global W π k b3 b4 b6
    h3 h4 h6 hπ a c p ha hp ψ hc hflat)
  exact h.trans (smoothPointAction_comp W (π ^ k) b3 b4 b6 h3 h4 h6
    (pow_ne_zero k hπ) e (q ≫ p) (q ≫ b) hb).symm

end FLT.Mazur.WeierstrassIntegralChart
