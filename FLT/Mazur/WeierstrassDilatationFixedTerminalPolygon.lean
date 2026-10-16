/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationFixedTerminalUnit
public import FLT.Mazur.NodalFiberUnitScalingGeometry
public import FLT.Mazur.PolygonInfinitesimalChartRestriction

/-!
# The whole terminal node in the fixed normalized polygon

The complete terminal chart uses the same target smoothing as the depth-one
initial and retained maps. The entire node isomorphism, its base map and its
polygon insertion commute with the original arithmetic quotient arrows.
Adjacent boundary agreement is a separate obligation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDilatation
open PolygonArithmeticStages WeierstrassModificationX WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (π : R)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
  (u : Rˣ) (hu : b6 = π * ↑u)
local notation "c" => fun m ↦ arithmeticTerminalSmoothing π m W s b3 b4 b6 ha hs h2 h4 h6
local notation "τ" => fun m ↦ arithmeticInitialMobiusSmoothing W ha (π ^ 1) π m
local notation "v" => arithmeticFixedTerminalUnit π W s b3 b4 b6 ha hs h2 h3 h4 h6 u hu
local notation "hv" => arithmeticFixedTerminalUnit_spec π W s b3 b4 b6
  ha hs h2 h3 h4 h6 u hu
local notation "hn" => fun m ↦ Fact.mk
  (arithmeticInitialFactorRatioSmoothing_nilpotent W ha (π ^ 1) π m (by simp))

/-- An isomorphism of entire nodes using the fixed normalized initial smoothing. -/
def fixedTerminalPolygonIso (m : ℕ) :
    Spec (.of (NodalFiber.Coordinate (c m))) ≅
      PolygonSmoothing.chart (Quotient R π m) (τ m) :=
  NodalFiber.unitSmoothingIso (c m) (τ m) (v m) (hv m)

/-- The full terminal node maps to any specified label of the fixed normalized polygon. -/
def fixedTerminalPolygonMap (m k : ℕ) (i : Fin (2 * k + 3)) :
    Spec (.of (NodalFiber.Coordinate (c m))) ⟶
      arithmeticFactorRatioPolygon π m W (π ^ 1) ha (by simp) k :=
  (fixedTerminalPolygonIso π W s b3 b4 b6 ha hs h2 h3 h4 h6 u hu m).hom ≫
    @PolygonInfinitesimal.chart (Quotient R π m) _ (τ m) (hn m) (2 * k + 3) (by omega) i

instance fixedTerminalPolygonMap_isOpenImmersion (m k : ℕ) (i : Fin (2 * k + 3)) :
    IsOpenImmersion
      (fixedTerminalPolygonMap π W s b3 b4 b6 ha hs h2 h3 h4 h6 u hu m k i) := by
  unfold fixedTerminalPolygonMap
  exact IsOpenImmersion.comp _ _

/-- The entire terminal normalization preserves its coefficient structure. -/
@[reassoc] theorem fixedTerminalPolygonIso_structure (m : ℕ) :
    (fixedTerminalPolygonIso π W s b3 b4 b6 ha hs h2 h3 h4 h6 u hu m).hom ≫
      PolygonSmoothing.chartStructure (Quotient R π m) (τ m) =
        Spec.map (CommRingCat.ofHom
          (algebraMap (Quotient R π m) (NodalFiber.Coordinate (c m)))) :=
  NodalFiber.unitSmoothingIso_structure (c m) (τ m) (v m) (hv m)

variable [IsDomain R] (hπ : π ≠ 0)
include hπ
local notation "C" => fun m ↦ NodalFiber.coefficientRingMap (AlgHom.toRingHom (restriction R π m))
  (c (m + 1)) (c m)
  (arithmeticTerminalSmoothing_restriction R π m W s b3 b4 b6 ha hs h2 h4 h6)
local notation "T" => fun m ↦ PolygonSmoothing.ringMap (AlgHom.toRingHom (restriction R π m))
  (τ (m + 1)) (τ m) (arithmeticInitialMobiusSmoothing_restriction W ha (π ^ 1) π m)

/-- Both full normalized node charts commute with the original quotient arrow. -/
@[reassoc] theorem fixedTerminalPolygonIso_restriction (m : ℕ) :
    Spec.map (CommRingCat.ofHom (C m)) ≫
      (fixedTerminalPolygonIso π W s b3 b4 b6 ha hs h2 h3 h4 h6 u hu (m + 1)).hom =
    (fixedTerminalPolygonIso π W s b3 b4 b6 ha hs h2 h3 h4 h6 u hu m).hom ≫
      Spec.map (CommRingCat.ofHom (T m)) :=
  NodalFiber.unitSmoothingIso_coefficients _ _ _ _ _ _ _ _ _ _ _
    (congrArg Units.val (arithmeticFixedTerminalUnit_restriction π W s b3 b4 b6
      ha hs h2 h3 h4 h6 u hu hπ m))

/-- Every terminal polygon label follows the same fixed-target quotient map. -/
@[reassoc] theorem fixedTerminalPolygonMap_restriction
    (m k : ℕ) (i : Fin (2 * k + 3)) :
    Spec.map (CommRingCat.ofHom (C m)) ≫
      fixedTerminalPolygonMap π W s b3 b4 b6 ha hs h2 h3 h4 h6 u hu (m + 1) k i =
    fixedTerminalPolygonMap π W s b3 b4 b6 ha hs h2 h3 h4 h6 u hu m k i ≫
      arithmeticFactorRatioPolygonRestriction π m W (π ^ 1) ha (by simp) k := by
  let _ := hn m
  let _ := hn (m + 1)
  simp only [fixedTerminalPolygonMap, arithmeticFactorRatioPolygonRestriction, Category.assoc]
  rw [PolygonInfinitesimal.chart_parameterProjection,
    ← Category.assoc, ← Category.assoc]
  rw [fixedTerminalPolygonIso_restriction π W s b3 b4 b6 ha hs h2 h3 h4 h6 u hu hπ]

end FLT.Mazur.WeierstrassDilatation
