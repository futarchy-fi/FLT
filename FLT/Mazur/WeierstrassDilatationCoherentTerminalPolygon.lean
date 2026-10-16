/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationCoherentTerminalUnit
public import FLT.Mazur.NodalFiberUnitScalingGeometry
public import FLT.Mazur.PolygonInfinitesimalChartRestriction
public import FLT.Mazur.PolygonArithmeticStageRestriction

/-!
# Natural terminal comparisons to the arithmetic polygon

The chosen units now form a compatible system. The entire original terminal
node therefore maps to a fixed cyclic chart at every arithmetic order, with
commuting quotient squares and unchanged base morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDilatation
open PolygonArithmeticStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (π : R)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
  (u : Rˣ) (hu : b6 = π * ↑u)
local notation "c" => fun m ↦ arithmeticTerminalSmoothing π m W s b3 b4 b6 ha hs h2 h4 h6
local notation "v" => arithmeticCoherentTerminalUnit π W s b3 b4 b6
  ha hs h2 h3 h4 h6 u hu
local notation "hv" => arithmeticCoherentTerminalUnit_spec π W s b3 b4 b6
  ha hs h2 h3 h4 h6 u hu

/-- The full terminal comparison uses the compatible normalization factors. -/
def coherentTerminalPolygonIso (m : ℕ) :
    Spec (.of (NodalFiber.Coordinate (c m))) ≅
      PolygonSmoothing.chart (Quotient R π m) (parameter R π m) :=
  NodalFiber.unitSmoothingIso (c m) (parameter R π m) (v m) (hv m)

/-- The entire original terminal node maps into a specified cyclic polygon chart. -/
def coherentTerminalPolygonMap (m N : ℕ) (hN : 2 ≤ N) (i : Fin N) :
    Spec (.of (NodalFiber.Coordinate (c m))) ⟶ (family R π m N hN).left :=
  (coherentTerminalPolygonIso π W s b3 b4 b6 ha hs h2 h3 h4 h6 u hu m).hom ≫
    PolygonInfinitesimal.chart (Quotient R π m) (parameter R π m) N hN i

instance coherentTerminalPolygonMap_isOpenImmersion (m N : ℕ) (hN : 2 ≤ N) (i : Fin N) :
    IsOpenImmersion
      (coherentTerminalPolygonMap π W s b3 b4 b6 ha hs h2 h3 h4 h6 u hu m N hN i) := by
  unfold coherentTerminalPolygonMap
  exact IsOpenImmersion.comp _ _

/-- The natural terminal comparison is over the original arithmetic coefficient ring. -/
@[reassoc] theorem coherentTerminalPolygonMap_base (m N : ℕ) (hN : 2 ≤ N) (i : Fin N) :
    coherentTerminalPolygonMap π W s b3 b4 b6 ha hs h2 h3 h4 h6 u hu m N hN i ≫
      (family R π m N hN).hom =
        Spec.map (CommRingCat.ofHom
          (algebraMap (Quotient R π m) (NodalFiber.Coordinate (c m)))) := by
  rw [coherentTerminalPolygonMap, Category.assoc]
  change _ ≫ (_ ≫ PolygonInfinitesimal.toBase _ _ _ _) = _
  rw [PolygonInfinitesimal.chart_toBase]
  exact NodalFiber.unitSmoothingIso_structure (c m) (parameter R π m) (v m) (hv m)

variable [IsDomain R] (hπ : π ≠ 0)
include hπ
local notation "C" => fun m ↦ NodalFiber.coefficientRingMap (AlgHom.toRingHom (restriction R π m))
  (c (m + 1)) (c m)
  (arithmeticTerminalSmoothing_restriction R π m W s b3 b4 b6 ha hs h2 h4 h6)

/-- The entire terminal normalization commutes with the original quotient restriction. -/
@[reassoc] theorem coherentTerminalPolygonIso_restriction (m : ℕ) :
    Spec.map (CommRingCat.ofHom (C m)) ≫
      (coherentTerminalPolygonIso π W s b3 b4 b6 ha hs h2 h3 h4 h6 u hu (m + 1)).hom =
    (coherentTerminalPolygonIso π W s b3 b4 b6 ha hs h2 h3 h4 h6 u hu m).hom ≫
      Spec.map (CommRingCat.ofHom (PolygonSmoothing.ringMap (restriction R π m).toRingHom
        (parameter R π (m + 1)) (parameter R π m) (restriction_parameter R π m))) :=
  NodalFiber.unitSmoothingIso_coefficients _ _ _ _ _ _ _ _ _ _ _
    (arithmeticCoherentTerminalUnit_coe_restriction π W s b3 b4 b6
      ha hs h2 h3 h4 h6 u hu hπ m)

/-- The full terminal polygon maps preserve both the fixed label and the quotient order. -/
@[reassoc] theorem coherentTerminalPolygonMap_restriction
    (m N : ℕ) (hN : 2 ≤ N) (i : Fin N) :
    Spec.map (CommRingCat.ofHom (C m)) ≫
      coherentTerminalPolygonMap π W s b3 b4 b6 ha hs h2 h3 h4 h6 u hu (m + 1) N hN i =
    coherentTerminalPolygonMap π W s b3 b4 b6 ha hs h2 h3 h4 h6 u hu m N hN i ≫
      stageRestriction R π m N hN := by
  simp only [coherentTerminalPolygonMap, Category.assoc, stageRestriction]
  rw [PolygonInfinitesimal.chart_parameterProjection,
    ← Category.assoc, ← Category.assoc]
  rw [coherentTerminalPolygonIso_restriction π W s b3 b4 b6
    ha hs h2 h3 h4 h6 u hu hπ]

end FLT.Mazur.WeierstrassDilatation
