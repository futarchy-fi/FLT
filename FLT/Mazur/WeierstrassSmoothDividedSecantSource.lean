/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothDividedProductSource
public import FLT.Mazur.WeierstrassSecantSmoothPresentation
public import FLT.Mazur.WeierstrassDividedDepthData

/-!
# The ordinary secant source for the integral divided input

The secant open of the concrete product carries both the original divided input
and the genuine ordinary output. Flatness retains regularity of the original scale.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] {W : WeierstrassCurve R} {π : R} {k : ℕ}
  (d : WeierstrassDividedDepth.Data W π k)
local notation "H" => WeierstrassDilatation.Coordinate W (π ^ k) d.b3 d.b4 d.b6
local notation "S" => SmoothDividedProductRing W (π ^ k) d.b3 d.b4 d.b6
local notation "a" => smoothDividedLeft W (π ^ k) d.b3 d.b4 d.b6
local notation "c" => smoothDividedRight W (π ^ k) d.b3 d.b4 d.b6
  d.factor3 d.factor4 d.factor6
local notation "p" => smoothDividedPoint W (π ^ k) d.b3 d.b4 d.b6
local notation "orig" => WeierstrassDilatation.fromOriginal W (π ^ k) d.b3 d.b4 d.b6
  d.factor3 d.factor4 d.factor6

/-- The concrete ordinary refinement of the integral divided product. -/
abbrev SmoothDividedSecantRing := SecantPairRing W a c

local notation "T" => SmoothDividedSecantRing d

/-- The genuine ordinary presentation on the divided secant source. -/
def smoothDividedSecantPresentation : additionChartRing W (ordinaryIndex false) →ₐ[R] T :=
  secantPairPresentation W a c

/-- The retained original divided input on the ordinary source. -/
def smoothDividedSecantInput : H →ₐ[R] T :=
  (IsScalarTower.toAlgHom R S T).comp (IsScalarTower.toAlgHom R H S)

/-- The original ordinary output before constructing its divided lift. -/
def smoothDividedSecantOutput : Coordinate W 2 →ₐ[R] T :=
  (smoothDividedSecantPresentation d).comp (ordinaryChartAddition W false)

/-- The constructed divided input contracts to exactly the ordinary right input. -/
theorem smoothDividedSecantInput_original :
    (smoothDividedSecantInput d).comp orig =
      (smoothDividedSecantPresentation d).comp (ordinaryInputRight W false) := by
  rw [smoothDividedSecantPresentation, secantPairPresentation_right]
  rfl

/-- Every original regular coefficient stays regular on the concrete secant source. -/
theorem smoothDividedSecant_base_regular {r : R} (hr : IsRegular r) :
    IsRegular (algebraMap R T r) := by
  have hH : IsRegular (algebraMap R H r) := flatRingHom_isRegular _
    (RingHom.flat_algebraMap_iff.mpr inferInstance) hr
  have hS := flatRingHom_isRegular _
    (smoothDividedInput_flat W (π ^ k) d.b3 d.b4 d.b6) hH
  have hT := flatRingHom_isRegular (algebraMap S T)
    (RingHom.flat_algebraMap_iff.mpr inferInstance) hS
  change IsRegular (algebraMap S T (algebraMap H S (algebraMap R H r))) at hT
  rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at hT

/-- The actual smooth point on the secant refinement. -/
def smoothDividedSecantPoint : Spec (.of T) ⟶ (integralSmoothOpen W).toScheme :=
  Spec.map (CommRingCat.ofHom (algebraMap S T)) ≫ p

/-- The two actual secant inputs retain their common original coefficient point. -/
theorem smoothDividedSecant_structure :
    smoothDividedSecantPoint d ≫ integralSmoothStructure W =
      (Spec.map (CommRingCat.ofHom
        (((IsScalarTower.toAlgHom R S T).comp c)).toRingHom) ≫ integralCurveChart W 2) ≫
          integralCurveStructure W :=
  secantPairSmooth_structure W a c p
    (smoothDivided_structure W (π ^ k) d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6)

/-- The original output is the genuine smooth translation on the integral cubic. -/
theorem smoothDividedSecantOutput_addition :
    Spec.map (CommRingCat.ofHom (smoothDividedSecantOutput d).toRingHom) ≫
        integralCurveChart W 2 =
      leftSmoothPointAddition W (smoothDividedSecantPoint d)
        (Spec.map (CommRingCat.ofHom
          ((IsScalarTower.toAlgHom R S T).comp c).toRingHom) ≫ integralCurveChart W 2)
        (smoothDividedSecant_structure d) :=
  secantPairSmooth_addition W a c p
    (smoothDividedLeft_inclusion W (π ^ k) d.b3 d.b4 d.b6)
    (smoothDivided_structure W (π ^ k) d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6)

end FLT.Mazur.WeierstrassIntegralChart
