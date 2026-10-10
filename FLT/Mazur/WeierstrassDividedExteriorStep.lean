/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthBoundary
public import FLT.Mazur.WeierstrassDividedExterior

/-!
# Repeating the actual divided-chart replacement

Attach the next x-direction chart to any preceding exterior, then glue its
actual deeper divided chart. The result carries its contraction to the
preceding whole scheme, with the existing actual depth transition on the
new divided chart. The output is again an exterior of the same form.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  {k : ℕ} (hπ : π ≠ 0) {d : Data W π k} (E : Exterior d) (e : Data W π (k + 1))

/-- Enlarge the exterior by the actual next x-direction chart. -/
def Exterior.advance : Exterior e where
  carrier := pushout E.attach (previousToX hπ d e)
  attach := nextToX e ≫ pushout.inr E.attach (previousToX hπ d e)

/-- The preceding exterior remains an open subscheme after enlargement. -/
def Exterior.retained : E.carrier ⟶ (E.advance hπ e).carrier := pushout.inl _ _

/-- The actual new x-direction chart is an open subscheme of the enlarged exterior. -/
def Exterior.newX : stepX e ⟶ (E.advance hπ e).carrier := pushout.inr _ _

instance Exterior.retained_isOpenImmersion : IsOpenImmersion (E.retained hπ e) := by
  unfold Exterior.retained
  infer_instance

instance Exterior.newX_isOpenImmersion : IsOpenImmersion (E.newX hπ e) := by
  unfold Exterior.newX
  infer_instance

/-- Every point of the enlarged exterior is retained or lies in the new actual x-chart. -/
theorem Exterior.advance_cover (z : (E.advance hπ e).carrier) :
    (∃ a, E.retained hπ e a = z) ∨ ∃ a, E.newX hπ e a = z :=
  SchemeOpenPushout.charts_cover E.attach (previousToX hπ d e) z

/-- The enlarged exterior maps to the preceding whole by the actual local contraction. -/
def Exterior.exteriorContraction : (E.advance hπ e).carrier ⟶ E.whole :=
  pushout.desc E.exteriorChart (xContraction hπ d e ≫ E.dividedChart) (by
    rw [previousToX_contraction_assoc]
    exact E.overlap)

/-- The contraction is unchanged on the retained exterior. -/
@[reassoc (attr := simp)] theorem Exterior.retained_contraction :
    E.retained hπ e ≫ E.exteriorContraction hπ e = E.exteriorChart :=
  pushout.inl_desc _ _ _

/-- The new x-chart retains its actual coordinate contraction. -/
@[reassoc (attr := simp)] theorem Exterior.newX_contraction :
    E.newX hπ e ≫ E.exteriorContraction hπ e = xContraction hπ d e ≫ E.dividedChart :=
  pushout.inr_desc _ _ _

/-- The new boundary contracts by the actual deeper divided transition. -/
@[reassoc] theorem Exterior.advance_boundary_contraction :
    (E.advance hπ e).attach ≫ E.exteriorContraction hπ e =
      boundaryInclusion e ≫ transition hπ d e ≫ E.dividedChart := by
  change (nextToX e ≫ E.newX hπ e) ≫ E.exteriorContraction hπ e = _
  rw [Category.assoc, Exterior.newX_contraction, nextToX_contraction_assoc]

/-- The actual next whole scheme contracts to the preceding whole scheme. -/
def Exterior.stepContraction : (E.advance hπ e).whole ⟶ E.whole :=
  pushout.desc (E.exteriorContraction hπ e) (transition hπ d e ≫ E.dividedChart)
    (E.advance_boundary_contraction hπ e)

/-- The whole contraction restricts to the constructed exterior contraction. -/
@[reassoc (attr := simp)] theorem Exterior.exteriorChart_stepContraction :
    (E.advance hπ e).exteriorChart ≫ E.stepContraction hπ e =
      E.exteriorContraction hπ e := pushout.inl_desc _ _ _

/-- On the deeper divided chart the whole contraction is exactly the actual depth map. -/
@[reassoc (attr := simp)] theorem Exterior.dividedChart_stepContraction :
    (E.advance hπ e).dividedChart ≫ E.stepContraction hπ e =
      transition hπ d e ≫ E.dividedChart := pushout.inr_desc _ _ _

/-- The old exterior inclusion is retained under whole contraction. -/
@[reassoc] theorem Exterior.retained_whole_contraction :
    E.retained hπ e ≫ (E.advance hπ e).exteriorChart ≫ E.stepContraction hπ e =
      E.exteriorChart := by simp

end FLT.Mazur.WeierstrassDividedDepth
