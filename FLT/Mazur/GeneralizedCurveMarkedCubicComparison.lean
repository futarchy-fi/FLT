/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingFamilyMorphism
public import FLT.Mazur.GeneralizedCurveMarkingCubicExt

/-!
# Canonical cubic comparison for independently named marked families

An isomorphism carrying the original smooth point constructs a pointed cubic
isomorphism for any two frames. Its compatibility with the whole-curve map
determines it uniquely; schematic density suffices for higher polygons.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback smoothMarkingWeierstrassCurve

/-- A frame of the original Cartier line restricted to its smooth marking. -/
abbrev SmoothMarkingFrame {S : Scheme} (E : GeneralizedEllipticCurve S)
    (s : 𝟙_ (Over S) ⟶ E.group) :=
  (pullback (s ≫ E.inclusion).left).obj
    (divisorLineBundle (s ≫ E.inclusion).left.ker
      (smoothMarking_relativeCartier E s).1) ≅ structureModule S

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  {E F : GeneralizedEllipticCurve S} (e : E ≅ F)
  (s : 𝟙_ (Over S) ⟶ E.group) (t : 𝟙_ (Over S) ⟶ F.group)
  (hs : s ≫ e.hom.group = t) (a : SmoothMarkingFrame E s) (b : SmoothMarkingFrame F t)
local notation "W" => smoothMarkingWeierstrassCurve E s a
local notation "V" => smoothMarkingWeierstrassCurve F t b

include hs in
/-- The independently named marking has a constructed pointed whole-cubic comparison. -/
theorem exists_markedCubicComparison :
    ∃ i : integralCurve (V) ≅ integralCurve (W),
      i.hom ≫ integralCurveStructure (W) = integralCurveStructure (V) ∧
      integralCurveZero (V) ≫ i.hom = integralCurveZero (W) ∧
      smoothMarkingToIntegralCubic F t b ≫ i.hom =
        e.inv.curve.left ≫ smoothMarkingToIntegralCubic E s a := by
  subst t
  exact exists_smoothMarkingFamilyCubicIso e s a b

/-- The comparison is obtained from the actual family, point and frames. -/
def markedCubicComparison : integralCurve (V) ≅ integralCurve (W) :=
  (exists_markedCubicComparison e s t hs a b).choose

/-- The constructed comparison preserves the coefficient base. -/
@[reassoc] theorem markedCubicComparison_over :
    (markedCubicComparison e s t hs a b).hom ≫ integralCurveStructure (W) =
      integralCurveStructure (V) :=
  (exists_markedCubicComparison e s t hs a b).choose_spec.1

/-- The constructed comparison preserves the marked infinity section. -/
@[reassoc] theorem markedCubicComparison_zero :
    integralCurveZero (V) ≫ (markedCubicComparison e s t hs a b).hom =
      integralCurveZero (W) :=
  (exists_markedCubicComparison e s t hs a b).choose_spec.2.1

/-- The comparison retains the actual map on the entire original family. -/
@[reassoc] theorem markedCubicComparison_whole :
    smoothMarkingToIntegralCubic F t b ≫ (markedCubicComparison e s t hs a b).hom =
      e.inv.curve.left ≫ smoothMarkingToIntegralCubic E s a :=
  (exists_markedCubicComparison e s t hs a b).choose_spec.2.2

/-- The original whole-curve square uniquely determines the comparison over the base. -/
theorem markedCubicComparison_unique (f : integralCurve (V) ⟶ integralCurve (W))
    (hf : f ≫ integralCurveStructure (W) = integralCurveStructure (V))
    (hw : smoothMarkingToIntegralCubic F t b ≫ f =
      e.inv.curve.left ≫ smoothMarkingToIntegralCubic E s a) :
    f = (markedCubicComparison e s t hs a b).hom := by
  apply smoothMarkingToIntegralCubic_hom_ext F t b (integralCurveStructure (W))
  · rw [hf, markedCubicComparison_over]
  · rw [hw, markedCubicComparison_whole]

end FLT.Mazur.GeneralizedEllipticCurve
