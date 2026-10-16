/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationArithmeticTerminalUnit
public import FLT.Mazur.NodalFiberUnitScaling
public import FLT.Mazur.PolygonArithmeticStageFamilies

/-!
# The original terminal node maps to the arithmetic polygon

A primitive b6 constructs the unit needed to identify the complete terminal
node with a uniform-parameter polygon chart. This is a fixed-order comparison;
compatibility of the chosen units across orders is separate work.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDilatation
open PolygonArithmeticStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
  (u : Rˣ) (hu : b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "c" => arithmeticTerminalSmoothing π m W s b3 b4 b6 ha hs h2 h4 h6

/-- A unit normalizing the actual terminal smoothing at this arithmetic order. -/
def arithmeticTerminalPolygonUnit : Qˣ :=
  Classical.choose (arithmeticTerminalSmoothing_exists_unit π m W s b3 b4 b6
    ha hs h2 h3 h4 h6 u hu)

local notation "v" => arithmeticTerminalPolygonUnit π m W s b3 b4 b6
  ha hs h2 h3 h4 h6 u hu

/-- The selected unit satisfies the original smoothing equation exactly. -/
theorem arithmeticTerminalPolygonUnit_spec : c = parameter R π m * ↑v :=
  Classical.choose_spec (arithmeticTerminalSmoothing_exists_unit π m W s b3 b4 b6
    ha hs h2 h3 h4 h6 u hu)

/-- The complete original node ring, including its origin, is a polygon chart ring. -/
def arithmeticTerminalPolygonEquiv :
    NodalFiber.Coordinate c ≃ₐ[Q] PolygonSmoothing.ChartRing (parameter R π m) :=
  NodalFiber.unitSmoothingEquiv c (parameter R π m) v
    (arithmeticTerminalPolygonUnit_spec π m W s b3 b4 b6 ha hs h2 h3 h4 h6 u hu)

/-- The full scheme comparison uses the explicitly constructed terminal unit. -/
def arithmeticTerminalPolygonIso :
    Spec (.of (NodalFiber.Coordinate c)) ≅ PolygonSmoothing.chart Q (parameter R π m) :=
  (Scheme.Spec.mapIso (arithmeticTerminalPolygonEquiv π m W s b3 b4 b6
    ha hs h2 h3 h4 h6 u hu).toRingEquiv.toCommRingCatIso.op).symm

/-- The original first factor carries the constructed unit correction. -/
theorem arithmeticTerminalPolygonEquiv_p :
    arithmeticTerminalPolygonEquiv π m W s b3 b4 b6 ha hs h2 h3 h4 h6 u hu
      (NodalFiber.p c) = algebraMap Q _ (↑v : Q) *
        PolygonSmoothing.leftCoordinate (parameter R π m) := by
  simp only [arithmeticTerminalPolygonEquiv, NodalFiber.unitSmoothingEquiv_p]

/-- The original second factor survives the full normalization unchanged. -/
theorem arithmeticTerminalPolygonEquiv_q :
    arithmeticTerminalPolygonEquiv π m W s b3 b4 b6 ha hs h2 h3 h4 h6 u hu
      (NodalFiber.q c) = PolygonSmoothing.rightCoordinate (parameter R π m) := by
  simp only [arithmeticTerminalPolygonEquiv, NodalFiber.unitSmoothingEquiv_q]

/-- A specific map from the entire terminal node into the intended cyclic chart. -/
def arithmeticTerminalPolygonMap (N : ℕ) (hN : 2 ≤ N) (i : Fin N) :
    Spec (.of (NodalFiber.Coordinate c)) ⟶ (family R π m N hN).left :=
  (arithmeticTerminalPolygonIso π m W s b3 b4 b6 ha hs h2 h3 h4 h6 u hu).hom ≫
    PolygonInfinitesimal.chart Q (parameter R π m) N hN i

instance arithmeticTerminalPolygonMap_isOpenImmersion (N : ℕ) (hN : 2 ≤ N) (i : Fin N) :
    IsOpenImmersion
      (arithmeticTerminalPolygonMap π m W s b3 b4 b6 ha hs h2 h3 h4 h6 u hu N hN i) := by
  unfold arithmeticTerminalPolygonMap
  exact IsOpenImmersion.comp _ _

end FLT.Mazur.WeierstrassDilatation
