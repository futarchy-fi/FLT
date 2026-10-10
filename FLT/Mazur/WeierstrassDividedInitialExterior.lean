/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedExterior
public import FLT.Mazur.WeierstrassModificationGluing

/-!
# Starting an exterior iteration from the actual modification

The original x-direction chart gives an exterior for any actual depth datum.
Its whole scheme is isomorphic to the existing two-chart modification,
preserving both charts and the original cubic contraction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] {W : WeierstrassCurve R} {π : R}
  {k : ℕ} (d : Data W π k)
open WeierstrassModificationX

/-- The original actual x-direction chart supplies the initial exterior. -/
def initialExterior : Exterior d where
  carrier := Spec (.of (Coordinate W (π ^ k) d.b3 d.b4 d.b6))
  attach := (overlapIso W (π ^ k) d.b3 d.b4 d.b6).inv ≫
    xOpenInclusion W (π ^ k) d.b3 d.b4 d.b6

/-- Changing the overlap coordinates identifies this whole with the original modification. -/
def initialExteriorIso : (initialExterior d).whole ≅
    modification W (π ^ k) d.b3 d.b4 d.b6 :=
  asIso (pushout.map _ _ (xOpenInclusion W (π ^ k) d.b3 d.b4 d.b6)
    (overlapToDivided W (π ^ k) d.b3 d.b4 d.b6) (𝟙 _) (𝟙 _)
    (overlapIso W (π ^ k) d.b3 d.b4 d.b6).inv
    (by simp [initialExterior]) (by simp [overlapToDivided]; rfl))

/-- The initial exterior chart is the original x-direction chart. -/
@[reassoc] theorem initialExteriorIso_exterior :
    (initialExterior d).exteriorChart ≫ (initialExteriorIso d).hom =
      xChart W (π ^ k) d.b3 d.b4 d.b6 := by
  simp [initialExteriorIso, Exterior.exteriorChart, xChart]

/-- The initial divided chart is the original actual divided chart. -/
@[reassoc] theorem initialExteriorIso_divided :
    (initialExterior d).dividedChart ≫ (initialExteriorIso d).hom =
      WeierstrassModificationX.dividedChart W (π ^ k) d.b3 d.b4 d.b6 := by
  simp [initialExteriorIso, Exterior.dividedChart, WeierstrassModificationX.dividedChart]

/-- The actual initial whole contracts to the original projective cubic. -/
def initialToCurve : (initialExterior d).whole ⟶ WeierstrassIntegralChart.integralCurve W :=
  (initialExteriorIso d).hom ≫
    contraction W (π ^ k) d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6

/-- The initial divided chart keeps its original cubic coordinates. -/
@[reassoc] theorem initialToCurve_divided :
    (initialExterior d).dividedChart ≫ initialToCurve d = toCurve d := by
  rw [initialToCurve, initialExteriorIso_divided_assoc, dividedChart_contraction]
  rfl

/-- The initial exterior keeps its original cubic coordinates. -/
@[reassoc] theorem initialToCurve_exterior :
    (initialExterior d).exteriorChart ≫ initialToCurve d =
      WeierstrassModificationX.toCurve W (π ^ k) d.b3 d.b4 d.b6
        d.factor3 d.factor4 d.factor6 := by
  rw [initialToCurve, initialExteriorIso_exterior_assoc, xChart_contraction]

end FLT.Mazur.WeierstrassDividedDepth
