/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SchemeOpenPushoutCharts
public import FLT.Mazur.WeierstrassDividedDepthData

/-!
# An arbitrary exterior for an actual divided chart

An exterior supplies just a scheme and an open embedding of the actual
horizontal boundary. The whole scheme is constructed by gluing, so an
exterior can contain any number of preceding x-direction charts.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] {W : WeierstrassCurve R} {π : R}
  {k : ℕ} (d : Data W π k)

/-- Geometric input for gluing an exterior to the actual divided chart. -/
structure Exterior where
  /-- The unchanged part of the whole scheme. -/
  carrier : Scheme
  /-- The actual boundary embeds as an open subscheme of the exterior. -/
  attach : boundary d ⟶ carrier
  open_attach : IsOpenImmersion attach := by infer_instance

attribute [instance] Exterior.open_attach

variable {d} (E : Exterior d)

/-- The actual whole scheme formed from the exterior and the divided chart. -/
def Exterior.whole : Scheme := pushout E.attach (boundaryInclusion d)

/-- The retained exterior is an open subscheme of the whole. -/
def Exterior.exteriorChart : E.carrier ⟶ E.whole := pushout.inl _ _

/-- The actual divided equation chart is an open subscheme of the whole. -/
def Exterior.dividedChart : chart d ⟶ E.whole := pushout.inr _ _

instance Exterior.exteriorChart_isOpenImmersion : IsOpenImmersion E.exteriorChart := by
  unfold Exterior.exteriorChart
  infer_instance

instance Exterior.dividedChart_isOpenImmersion : IsOpenImmersion E.dividedChart := by
  unfold Exterior.dividedChart
  infer_instance

/-- The two actual chart inclusions agree along the prescribed boundary. -/
@[reassoc] theorem Exterior.overlap :
    E.attach ≫ E.exteriorChart = boundaryInclusion d ≫ E.dividedChart := pushout.condition

/-- Every point belongs to the exterior or the actual divided chart. -/
theorem Exterior.charts_cover (z : E.whole) :
    (∃ a, E.exteriorChart a = z) ∨ ∃ a, E.dividedChart a = z :=
  SchemeOpenPushout.charts_cover E.attach (boundaryInclusion d) z

/-- Maps from the two actual charts determine a map from the whole scheme. -/
@[ext] theorem Exterior.hom_ext {Y : Scheme} {f g : E.whole ⟶ Y}
    (he : E.exteriorChart ≫ f = E.exteriorChart ≫ g)
    (hd : E.dividedChart ≫ f = E.dividedChart ≫ g) : f = g :=
  pushout.hom_ext he hd

end FLT.Mazur.WeierstrassDividedDepth
