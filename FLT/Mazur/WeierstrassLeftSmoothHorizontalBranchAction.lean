/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothHorizontalResidueFactor
public import FLT.Mazur.WeierstrassLeftSmoothHorizontalResidueAction

/-!
# Actual horizontal branch action with the residue factorization constructed

The residue source starts on the original input presentation. Its map into
the output quotient open is constructed from the proved branch character.
The resulting genuine action lift scales the original scale/X coordinate by
the normalized smooth parameter or its inverse, and preserves the branch.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  (W : WeierstrassCurve R) (π : R) {depth k : ℕ} (b3 b4 b6 : R)
  (D : SplitNodeDepth W π depth) (d : WeierstrassDividedDepth.Data W π k)
  (hk : 2 * k ≤ depth) (hdepth : 0 < depth)
  (h3 : W.a₃ = (π ^ k) * b3) (h4 : W.a₄ = (π ^ k) * b4) (h6 : W.a₆ = (π ^ k) * b6)
  {S : Type u} [CommRing S] [Algebra R S]
  (p : Spec (.of S) ⟶ (integralSmoothOpen W).toScheme) (α β : Coordinate W 2 →+* S)
  (hp : p ≫ integralSmoothStructure W =
    (Spec.map (CommRingCat.ofHom β) ≫ integralCurveChart W 2) ≫ integralCurveStructure W)
  (hα : Spec.map (CommRingCat.ofHom α) ≫ integralCurveChart W 2 =
    leftSmoothPointAddition W p (Spec.map (CommRingCat.ofHom β) ≫ integralCurveChart W 2) hp)

local notation "I" => modificationChartCenter W (π ^ k) 2
local notation "x" => coord W 2 0
local notation "hx" => WeierstrassModificationReesCoordinates.centerGenerators_mem W (π ^ k) 1
variable (ψ : BlowupFractionChart.chart (modificationChartCenter W (π ^ k) 2) (coord W 2 0) →+* S)
  (hβ : β = ψ.comp
    (algebraMap (Coordinate W 2)
      (BlowupFractionChart.chart (modificationChartCenter W (π ^ k) 2) (coord W 2 0))))
  (hflat : RingHom.Flat
    (R := BlowupFractionChart.chart (modificationChartCenter W (π ^ k) 2) (coord W 2 0)) (S := S) ψ)

open RegularCenter BlowupFractionChart
local notation "z" => ψ (denominator I x)
local notation "H" => leftSmoothFractionAction_principal W (π ^ k) b3 b4 b6
  h3 h4 h6 p α β hp hα x hx ψ hβ
local notation "Q" => quotient I α z H
local notation "O" => LeftSmoothFractionActionOpen W (π ^ k) b3 b4 b6
  h3 h4 h6 p α β hp hα x hx ψ hβ 1

open WeierstrassModificationReesCoordinates IsLocalRing
variable (b : Bool) (f : additionChartRing W (ordinaryIndex b) →ₐ[R] S)
  (hβf : β = (f.comp (ordinaryInputRight W b)).toRingHom)
  (hαf : α = (f.comp (ordinaryChartAddition W b)).toRingHom)
  {C : Type u} [CommRing C] (e : S →+* C) (he : e (ψ (denominator
    (modificationChartCenter W (π ^ k) 2) (coord W 2 0))) = 0)
  (hJ : (maximalIdeal R).map (algebraMap R S) ≤ RingHom.ker e)
  (v : Fin 3 → C)
  (hv : ∀ i, e (f (ordinaryInputLeft W b (coord W 2 i))) =
    e (f (ordinaryInputLeft W b (coord W 2 1))) * v i)
  (hbranch : e (ψ (horizontalVertical W (π ^ k))) = 0 ∨
    e (ψ (horizontalVertical W (π ^ k))) = -e (algebraMap R S W.a₁))

local notation "E" => leftSmoothHorizontalResidueFactor W π b3 b4 b6 D d hk hdepth
  h3 h4 h6 p α β hp hα ψ hβ hflat b f hβf hαf e he hJ v hv hbranch
local notation "M" => leftSmoothFractionActionLift W (π ^ k) b3 b4 b6
  h3 h4 h6 p α β hp hα x hx ψ hβ hflat 1

/-- The genuine action on both branches, with the output residue factorization constructed. -/
theorem leftSmoothHorizontalBranch_action (τ : Cˣ)
    (hτ : (τ : C) = 1 + e (algebraMap R S W.a₁) * v 0) :
    (e (ψ (horizontalVertical W (π ^ k))) = 0 →
      E (M (horizontalScale W (π ^ k))) = (τ : C) * e (ψ (horizontalScale W (π ^ k))) ∧
        E (M (horizontalVertical W (π ^ k))) = 0) ∧
    (e (ψ (horizontalVertical W (π ^ k))) = -e (algebraMap R S W.a₁) →
      E (M (horizontalScale W (π ^ k))) =
          (↑τ⁻¹ : C) * e (ψ (horizontalScale W (π ^ k))) ∧
        E (M (horizontalVertical W (π ^ k))) = -e (algebraMap R S W.a₁)) := by
  have hb (t : S) : E (algebraMap S O t) = e t :=
    leftSmoothHorizontalResidueFactor_base W π b3 b4 b6 D d hk hdepth
      h3 h4 h6 p α β hp hα ψ hβ hflat b f hβf hαf e he hJ v hv hbranch t
  have hE : (E).comp (algebraMap S O) = e := RingHom.ext hb
  have result := leftSmoothHorizontalAction_normalized W π b3 b4 b6 D d hk hdepth
    h3 h4 h6 p α β hp hα ψ hβ hflat b f hβf hαf E (by rw [hb]; exact he)
    (by rw [hE]; exact hJ) v (by intro i; simpa only [hb] using hv i) τ
    (by simpa only [hb] using hτ)
  simpa only [leftSmoothHorizontalInputLift, RingHom.comp_apply, hb] using result

end FLT.Mazur.WeierstrassIntegralChart
