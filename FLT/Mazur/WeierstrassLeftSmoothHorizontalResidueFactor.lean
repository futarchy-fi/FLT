/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothHorizontalActionPresentation
public import FLT.Mazur.WeierstrassSplitDepthHorizontalOutputUnit
public import FLT.Mazur.WeierstrassSplitDepthAffineParameters

/-!
# Exceptional branches factor through the actual output horizontal open

The residue unit is derived on the original input presentation from the
conormal character and input quotient one. Localization then constructs the
map into the named output open; it is not a premise of the branch calculation.
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

include D d hk hdepth hflat hβf hαf he hJ hv hbranch in
/-- The actual output X quotient is a residue unit before passing to its quotient open. -/
theorem leftSmoothHorizontalResidue_unit : IsUnit (e (Q x hx)) := by
  let I' := (I).map (f.comp (ordinaryInputRight W b)).toRingHom
  have hxi : f (ordinaryInputRight W b x) = z :=
    (DFunLike.congr_fun hβf x).symm.trans
      (leftSmoothHorizontalInput_denominator W (π ^ k) β ψ hβ)
  have hi : I'.map (RingHom.id S) =
      Ideal.span {f (ordinaryInputRight W b x)} := by
    rw [Ideal.map_id, hxi]
    change (I).map (f.comp (ordinaryInputRight W b)).toRingHom = _
    rw [← hβf, hβ]
    exact center_map_eq_mapped_denominator I x hx ψ
  have hz : IsRegular z := flatRingHom_isRegular ψ hflat (denominator_regular I x)
  have hL (t : Coordinate W 2) : ψ (algebraMap _ _ t) =
      f (ordinaryInputRight W b t) :=
    (DFunLike.congr_fun hβ t).symm.trans (DFunLike.congr_fun hβf t)
  obtain ⟨r, q, hq, hr, hy, _⟩ := splitDepthAffine_exists_normalized_units
    D hdepth (f.comp (ordinaryInputLeft W b)) e hJ v hv
  have hu := splitDepthHorizontal_output_unit D d hk b f hi (hxi ▸ hz) ψ hL e
    (hxi ▸ he) hJ r q hr hy hq hbranch
  have hquot : quotient I' (RingHom.id S) (f (ordinaryInputRight W b x)) hi
      (f (ordinaryChartAddition W b x)) (splitDepthExceptional_coordinates_mem d b f).2.1 =
        Q x hx := by
    apply quotient_unique I α z H hz
    have hmul := denominator_mul_quotient I' (RingHom.id S)
      (f (ordinaryInputRight W b x)) hi (f (ordinaryChartAddition W b x))
      (splitDepthExceptional_coordinates_mem d b f).2.1
    rw [← hxi]
    exact hmul.trans (DFunLike.congr_fun hαf x).symm
  rw [hquot] at hu
  exact hu

/-- The original branch residue map canonically factors through the named horizontal action open. -/
def leftSmoothHorizontalResidueFactor : O →+* C := by
  change Localization.Away (Q x hx) →+* C
  exact IsLocalization.Away.lift (Q x hx)
    (leftSmoothHorizontalResidue_unit W π b3 b4 b6 D d hk hdepth h3 h4 h6
      p α β hp hα ψ hβ hflat b f hβf hαf e he hJ v hv hbranch)

/-- The constructed factorization recovers every function of the original residue source. -/
@[simp] theorem leftSmoothHorizontalResidueFactor_base (t : S) :
    leftSmoothHorizontalResidueFactor W π b3 b4 b6 D d hk hdepth h3 h4 h6
      p α β hp hα ψ hβ hflat b f hβf hαf e he hJ v hv hbranch (algebraMap S O t) = e t :=
  IsLocalization.Away.lift_eq (S := Localization.Away (Q x hx)) _
    (leftSmoothHorizontalResidue_unit W π b3 b4 b6 D d hk hdepth h3 h4 h6
      p α β hp hα ψ hβ hflat b f hβf hαf e he hJ v hv hbranch) t

end FLT.Mazur.WeierstrassIntegralChart
