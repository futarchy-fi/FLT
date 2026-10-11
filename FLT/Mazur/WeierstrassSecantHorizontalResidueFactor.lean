/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSecantHorizontalInput
public import FLT.Mazur.WeierstrassSplitDepthSecantResidue
public import FLT.Mazur.WeierstrassLeftSmoothHorizontalResidueFactor

/-!
# A concrete ordinary refinement and horizontal output factorization

Starting with the actual smooth affine/Y input and a flat original horizontal
fraction presentation, both localizations are constructed: first the secant
open, then the genuine output horizontal quotient open. Every branch residue
map lifts through their composite without assuming an ordinary presentation
or an output quotient factorization.
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

omit [IsDomain R] [IsLocalRing R] in
include hc in
/-- The refined ordinary right input contracts to the actual original horizontal chart. -/
theorem secantHorizontal_beta : β = (ψ').comp (algebraMap (Coordinate W 2)
    (BlowupFractionChart.chart (modificationChartCenter W (π ^ k) 2) (coord W 2 0))) := by
  have h := secantHorizontalInput_contraction W (π ^ k) a c ψ hc
  rw [secantPairPresentation_right] at h
  exact h

local notation "hβ" => secantHorizontal_beta W π a c ψ hc
local notation "O" => LeftSmoothFractionActionOpen W (π ^ k) b3 b4 b6
  h3 h4 h6 p' α β hp' hα x hx ψ' hβ 1

omit [IsDomain R] [IsLocalRing R] in
include hc he in
/-- Vanishing of the retained original denominator is the original nodal X condition. -/
theorem secantHorizontal_residue_node : e (c x) = 0 := by
  rw [show c x = ψ (BlowupFractionChart.denominator
      (modificationChartCenter W (π ^ k) 2) x) from
    leftSmoothHorizontalInput_denominator W (π ^ k) c.toRingHom ψ hc]
  exact he

local notation "e'" => splitDepthSecantResidue D hdepth a c v hv e hJ
  (secantHorizontal_residue_node W π c ψ hc e he)

/-- The branch residue factorization through both concrete action refinements. -/
def secantHorizontalResidueFactor : O →+* C := by
  have hβf : β = ((f).comp (ordinaryInputRight W false)).toRingHom :=
    (congrArg AlgHom.toRingHom (secantPairPresentation_right W a c)).symm
  have base (t : S) : e' (algebraMap S T t) = e t := splitDepthSecantResidue_base ..
  have hJ' : (maximalIdeal R).map (algebraMap R T) ≤ RingHom.ker e' := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change e' (algebraMap R T r) = 0
    rw [IsScalarTower.algebraMap_apply R S T, base]
    exact hJ (Ideal.mem_map_of_mem _ hr)
  have he' : e' (ψ' (BlowupFractionChart.denominator
      (modificationChartCenter W (π ^ k) 2) x)) = 0 := by
    change e' (algebraMap S T (ψ _)) = 0
    rw [base]
    exact he
  have hbranch' :
      e' (ψ' (WeierstrassModificationReesCoordinates.horizontalVertical W (π ^ k))) = 0 ∨
      e' (ψ' (WeierstrassModificationReesCoordinates.horizontalVertical W (π ^ k))) =
        -e' (algebraMap R T W.a₁) := by
    change e' (algebraMap S T (ψ _)) = 0 ∨
      e' (algebraMap S T (ψ _)) = -e' (algebraMap R T W.a₁)
    rw [base, IsScalarTower.algebraMap_apply R S T, base]
    exact hbranch
  exact leftSmoothHorizontalResidueFactor W π b3 b4 b6 D d hk hdepth h3 h4 h6
    p' α β hp' hα ψ' hβ (secantHorizontalInput_flat W (π ^ k) a c ψ hflat)
    false f hβf rfl e' he' hJ' (fun i => e' (algebraMap S T (v (coord W 1 i))))
    (secantPairSmooth_cross W a c v hv e') hbranch'

/-- Every original residue function is preserved by the composite localization factorization. -/
theorem secantHorizontalResidueFactor_base (t : S) :
    secantHorizontalResidueFactor W π D d hk hdepth b3 b4 b6 h3 h4 h6
      a c v p ha hp hv ψ hc hflat e he hJ hbranch (algebraMap S O t) = e t := by
  unfold secantHorizontalResidueFactor
  rw [IsScalarTower.algebraMap_apply S T O, leftSmoothHorizontalResidueFactor_base]
  exact splitDepthSecantResidue_base ..

end FLT.Mazur.WeierstrassIntegralChart
