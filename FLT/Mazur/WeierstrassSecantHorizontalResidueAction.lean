/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSecantHorizontalResidueFactor
public import FLT.Mazur.WeierstrassLeftSmoothHorizontalResidueAction

/-!
# Normalized action on the constructed secant horizontal refinement

The residue factor is the actual composite localization map. Its action on
both branches uses the original smooth input and the original horizontal
coordinates, before either refinement.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S C : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  [CommRing S] [Algebra R S] [CommRing C]
  (W : WeierstrassCurve R) (π : R) {depth k : ℕ}
  (D : SplitNodeDepth W π depth) (d : WeierstrassDividedDepth.Data W π k)
  (hk : 2 * k ≤ depth) (hdepth : 0 < depth) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4) (h6 : W.a₆ = π ^ k * b6)
  (a c : Coordinate W 2 →ₐ[R] S) (v : Coordinate W 1 →ₐ[R] S)
  (p : Spec (.of S) ⟶ (integralSmoothOpen W).toScheme)
  (ha : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ integralCurveChart W 2 =
    p ≫ (integralSmoothOpen W).ι)
  (hp : p ≫ integralSmoothStructure W =
    (Spec.map (CommRingCat.ofHom c.toRingHom) ≫ integralCurveChart W 2) ≫
      integralCurveStructure W)
  (hv : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ integralCurveChart W 2 =
    Spec.map (CommRingCat.ofHom v.toRingHom) ≫ integralCurveChart W 1)
  (ψ : BlowupFractionChart.chart (modificationChartCenter W (π ^ k) 2) (coord W 2 0) →+* S)
  (hc : c.toRingHom = ψ.comp (algebraMap (Coordinate W 2)
    (BlowupFractionChart.chart (modificationChartCenter W (π ^ k) 2) (coord W 2 0))))
  (hflat : RingHom.Flat ψ) (e : S →+* C)
  (he : e (ψ (BlowupFractionChart.denominator
    (modificationChartCenter W (π ^ k) 2) (coord W 2 0))) = 0)
  (hJ : (maximalIdeal R).map (algebraMap R S) ≤ RingHom.ker e)
  (hbranch : e (ψ (WeierstrassModificationReesCoordinates.horizontalVertical W (π ^ k))) = 0 ∨
    e (ψ (WeierstrassModificationReesCoordinates.horizontalVertical W (π ^ k))) =
      -e (algebraMap R S W.a₁))
local notation "T" => SecantPairRing W a c
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "f" => secantPairPresentation W a c
local notation "β" => AlgHom.toRingHom (AlgHom.comp (IsScalarTower.toAlgHom R S T) c)
local notation "α" => AlgHom.toRingHom (AlgHom.comp f (ordinaryChartAddition W false))
local notation "p'" => Spec.map (CommRingCat.ofHom (algebraMap S T)) ≫ p
local notation "hp'" => secantPairSmooth_structure W a c p hp
local notation "hα" => secantPairSmooth_addition W a c p ha hp
local notation "ψ'" => secantHorizontalInput W (π ^ k) a c ψ
local notation "x" => coord W 2 0
local notation "hx" => WeierstrassModificationReesCoordinates.centerGenerators_mem W (π ^ k) 1

local notation "hβ" => secantHorizontal_beta W π a c ψ hc
local notation "O" => LeftSmoothFractionActionOpen W (π ^ k) b3 b4 b6
  h3 h4 h6 p' α β hp' hα x hx ψ' hβ 1
local notation "e'" => splitDepthSecantResidue D hdepth a c v hv e hJ
  (secantHorizontal_residue_node W π c ψ hc e he)
local notation "E" => secantHorizontalResidueFactor W π D d hk hdepth
  b3 b4 b6 h3 h4 h6 a c v p ha hp hv ψ hc hflat e he hJ hbranch

/-- The constructed output residue map also preserves every secant refinement function. -/
theorem secantHorizontalResidueFactor_secant (t : T) :
    E (algebraMap T O t) = e' t := by
  unfold secantHorizontalResidueFactor
  exact leftSmoothHorizontalResidueFactor_base ..

omit [IsDomain R] [IsLocalRing R] in
/-- The genuine action lift on the constructed ordinary and horizontal refinements. -/
def secantHorizontalActionLift :=
  leftSmoothFractionActionLift W (π ^ k) b3 b4 b6
    h3 h4 h6 p' α β hp' hα x hx ψ' hβ
    (secantHorizontalInput_flat W (π ^ k) a c ψ hflat) 1

local notation "M" => secantHorizontalActionLift W π b3 b4 b6 h3 h4 h6 a c p ha hp ψ hc hflat
omit [IsDomain R] [IsLocalRing R] in
/-- The constructed lift retains the original affine action coordinates. -/
theorem secantHorizontalActionLift_base (t : Coordinate W 2) :
    M (algebraMap (Coordinate W 2) _ t) = algebraMap T O (α t) := by
  unfold secantHorizontalActionLift
  exact leftSmoothFractionActionLift_base ..

open WeierstrassModificationReesCoordinates

/-- Both normalized branch characters hold for the actual composite refinement. -/
theorem secantHorizontalResidueFactor_action (τ : Cˣ)
    (hτ : (τ : C) = 1 + e (algebraMap R S W.a₁) * e (v (coord W 1 0))) :
    (e (ψ (horizontalVertical W (π ^ k))) = 0 →
      E (M (horizontalScale W (π ^ k))) = (τ : C) * e (ψ (horizontalScale W (π ^ k))) ∧
        E (M (horizontalVertical W (π ^ k))) = 0) ∧
    (e (ψ (horizontalVertical W (π ^ k))) = -e (algebraMap R S W.a₁) →
      E (M (horizontalScale W (π ^ k))) =
          (↑τ⁻¹ : C) * e (ψ (horizontalScale W (π ^ k))) ∧
        E (M (horizontalVertical W (π ^ k))) = -e (algebraMap R S W.a₁)) := by
  have base (t : T) : E (algebraMap T O t) = e' t :=
    secantHorizontalResidueFactor_secant ..
  have orig (t : S) : e' (algebraMap S T t) = e t := splitDepthSecantResidue_base ..
  have hJ' : (maximalIdeal R).map (algebraMap R T) ≤ RingHom.ker
      ((E).comp (algebraMap T O)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change E (algebraMap T O (algebraMap R T r)) = 0
    rw [base, IsScalarTower.algebraMap_apply R S T, orig]
    exact hJ (Ideal.mem_map_of_mem _ hr)
  have hβf : β = ((f).comp (ordinaryInputRight W false)).toRingHom :=
    (congrArg AlgHom.toRingHom (secantPairPresentation_right W a c)).symm
  have result := leftSmoothHorizontalAction_normalized W π b3 b4 b6 D d hk hdepth
    h3 h4 h6 p' α β hp' hα ψ' hβ
    (secantHorizontalInput_flat W (π ^ k) a c ψ hflat) false f hβf rfl E
    (by rw [base]; change e' (algebraMap S T (ψ _)) = 0; rw [orig]; exact he)
    hJ' (fun i => e' (algebraMap S T (v (coord W 1 i))))
    (by simpa only [base] using secantPairSmooth_cross W a c v hv e') τ
    (by rw [base, IsScalarTower.algebraMap_apply R S T, orig, orig]; exact hτ)
  have inp (q : BlowupFractionChart.chart
      (modificationChartCenter W (π ^ k) 2) x) :
      E (algebraMap T O (ψ' q)) = e (ψ q) := by
    rw [base]
    exact orig (ψ q)
  simpa only [secantHorizontalActionLift, leftSmoothHorizontalInputLift,
    RingHom.comp_apply, inp, base,
    IsScalarTower.algebraMap_apply R S T, orig] using result

end FLT.Mazur.WeierstrassIntegralChart
