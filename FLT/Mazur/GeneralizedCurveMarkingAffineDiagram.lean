/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingDirectCocycle
public import FLT.Mazur.GeneralizedCurveLocalMarkingFrames

/-!
# The diagram of all directly framed affine cubic charts

Objects consist only of an affine base open and an actual original marking
frame. Inclusions supply the thin category; the constructed restriction maps
and their proved laws supply the open scheme diagram.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback smoothMarkingWeierstrassCurve smoothMarkingDirectRestriction
variable {S : Scheme} (E : GeneralizedEllipticCurve S)
  (s : 𝟙_ (Over S) ⟶ E.group)

/-- An affine open with a frame on the actual directly restricted original marking. -/
structure SmoothMarkingAffineChart where
  /-- The original affine base open. -/
  base : S.affineOpens
  /-- An actual frame on the directly restricted original marking line. -/
  frame : SmoothMarkingFrame (E.baseChange base.1.ι) (pullSection base.1.ι s)

instance smoothMarkingAffineChartPreorder : Preorder (SmoothMarkingAffineChart E s) :=
  Preorder.lift (fun i ↦ i.base.1)

instance smoothMarkingAffineChart_affine (i : SmoothMarkingAffineChart E s) :
    IsAffine i.base.1.toScheme := i.base.2

/-- Directly framed affine opens refine every neighborhood of every original base point. -/
theorem exists_smoothMarkingAffineChart {V : S.Opens} {x : S} (hx : x ∈ V) :
    ∃ i : SmoothMarkingAffineChart E s, x ∈ i.base.1 ∧ i.base.1 ≤ V := by
  obtain ⟨U, hxU, hUV, ⟨a⟩⟩ := exists_smoothMarking_affineFrame E s hx
  exact ⟨⟨U, a⟩, hxU, hUV⟩

variable [IsLocallyNoetherian S]

local instance affineDiagramNoetherian (i : SmoothMarkingAffineChart E s) :
    IsNoetherianRing Γ(i.base.1.toScheme, ⊤) :=
  IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

/-- The actual cubic equation attached to a directly framed affine base chart. -/
def smoothMarkingAffineEquation (i : SmoothMarkingAffineChart E s) :
    WeierstrassCurve Γ(i.base.1.toScheme, ⊤) :=
  smoothMarkingWeierstrassCurve (E.baseChange i.base.1.ι) (pullSection i.base.1.ι s) i.frame

/-- The scheme diagram has proved functor laws, with no compatibility supplied as data. -/
def smoothMarkingAffineDiagram : SmoothMarkingAffineChart E s ⥤ Scheme where
  obj i := integralCurve (smoothMarkingAffineEquation E s i)
  map {i j} f := smoothMarkingDirectRestriction E s j.base.1 i.base.1 f.le j.frame i.frame
  map_id i := smoothMarkingDirectRestriction_refl E s i.base.1 i.frame
  map_comp {i j k} f g :=
    (smoothMarkingDirectRestriction_comp E s k.base.1 j.base.1 i.base.1
      k.frame j.frame i.frame f.le g.le).symm

/-- Every arrow in the actual cubic diagram is an open immersion. -/
instance smoothMarkingAffineDiagram_isOpenImmersion {i j : SmoothMarkingAffineChart E s}
    (f : i ⟶ j) : IsOpenImmersion ((smoothMarkingAffineDiagram E s).map f) :=
  smoothMarkingDirectRestriction_isOpenImmersion E s j.base.1 i.base.1 f.le j.frame i.frame

end FLT.Mazur.GeneralizedEllipticCurve
