/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingCubicOpenProjection

/-!
# Cubic restrictions inside actual affine frame opens

A frame on an affine open of an arbitrary locally Noetherian base transports
to every smaller affine open. The recomputed whole cubic maps by an open
immersion to the original chart, retaining the actual whole-family morphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback smoothMarkingWeierstrassCurve smoothMarkingTransportedFrame
variable {S : Scheme} [IsLocallyNoetherian S] (E : GeneralizedEllipticCurve S)
  (s : 𝟙_ (Over S) ⟶ E.group) (U W : S.Opens)
  [IsAffine U.toScheme] [IsAffine W.toScheme] (h : W ≤ U)
  (a : SmoothMarkingFrame (E.baseChange U.ι) (pullSection U.ι s))

local instance openCubicChartNoetherian : IsNoetherianRing Γ(U.toScheme, ⊤) :=
  IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

local instance openCubicRestrictionNoetherian : IsNoetherianRing Γ(W.toScheme, ⊤) :=
  IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

/-- The original chart frame transported to the smaller actual family. -/
def smoothMarkingOpenRestrictionFrame :
    SmoothMarkingFrame ((E.baseChange U.ι).baseChange (S.homOfLE h))
      (pullSection (S.homOfLE h) (pullSection U.ι s)) :=
  smoothMarkingTransportedFrame (E.baseChange U.ι) (S.homOfLE h) (pullSection U.ι s) a

/-- The equation is recomputed from the actual iterated restriction and transported frame. -/
def smoothMarkingOpenRestrictionEquation : WeierstrassCurve Γ(W.toScheme, ⊤) :=
  smoothMarkingWeierstrassCurve ((E.baseChange U.ι).baseChange (S.homOfLE h))
    (pullSection (S.homOfLE h) (pullSection U.ι s))
    (smoothMarkingOpenRestrictionFrame E s U W h a)

local notation "F" => GeneralizedEllipticCurve.baseChange (E.baseChange U.ι) (S.homOfLE h)
local notation "t" => pullSection (S.homOfLE h) (pullSection U.ι s)
local notation "b" => smoothMarkingOpenRestrictionFrame E s U W h a
local notation "V" => smoothMarkingOpenRestrictionEquation E s U W h a
local notation "C" => smoothMarkingWeierstrassCurve (E.baseChange U.ι) (pullSection U.ι s) a

/-- The actual smaller cubic projects to its original affine frame chart. -/
def smoothMarkingOpenRestrictionProjection : integralCurve V ⟶ integralCurve C :=
  smoothMarkingCubicProjection (E.baseChange U.ι) (S.homOfLE h) (pullSection U.ι s) a b

/-- The projection is an open immersion of whole cubics. -/
instance smoothMarkingOpenRestrictionProjection_isOpenImmersion :
    IsOpenImmersion (smoothMarkingOpenRestrictionProjection E s U W h a) :=
  smoothMarkingCubicProjection_isOpenImmersion _ _ _ _ _

/-- The restriction retains the actual whole original family map. -/
@[reassoc] theorem smoothMarkingOpenRestrictionProjection_whole :
    smoothMarkingToIntegralCubic F t b ≫ smoothMarkingOpenRestrictionProjection E s U W h a =
      Limits.pullback.fst (E.baseChange U.ι).curve.hom (S.homOfLE h) ≫
        smoothMarkingToIntegralCubic (E.baseChange U.ι) (pullSection U.ι s) a :=
  smoothMarkingToIntegralCubic_projection _ _ _ _ _

end FLT.Mazur.GeneralizedEllipticCurve
