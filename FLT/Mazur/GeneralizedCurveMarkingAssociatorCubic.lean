/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingAssociator
public import FLT.Mazur.GeneralizedCurveMarkingFamilyMorphism

/-!
# Independently recomputed cubics under the canonical base-change associator

The actual directly pulled family and the independently iterated family have
compatible whole-curve cubic maps. Both marking frames are arbitrary, and the
comparison preserves the coefficient base and infinity section.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback smoothMarkingWeierstrassCurve
variable {S T U : Scheme} [IsAffine U] [IsNoetherianRing Γ(U, ⊤)]
  (E : GeneralizedEllipticCurve S) (g : T ⟶ S) (h : U ⟶ T)
  (s : 𝟙_ (Over S) ⟶ E.group)
  (a : (pullback (pullSection (h ≫ g) s ≫ (E.baseChange (h ≫ g)).inclusion).left).obj
    (divisorLineBundle (pullSection (h ≫ g) s ≫ (E.baseChange (h ≫ g)).inclusion).left.ker
      (smoothMarking_relativeCartier (E.baseChange (h ≫ g)) (pullSection (h ≫ g) s)).1) ≅
        structureModule U)
local notation "D" => E.baseChange (h ≫ g)
local notation "F" => GeneralizedEllipticCurve.baseChange (E.baseChange g) h
local notation "sD" => pullSection (h ≫ g) s
local notation "sF" => pullSection h (pullSection g s)
local notation "W" => smoothMarkingWeierstrassCurve (D) (sD) a

/-- The actual associator compares independently framed whole cubic maps, retaining the point. -/
theorem smoothMarkingAssociator_cubic
    (b : (pullback (pullSection h (pullSection g s) ≫
      ((E.baseChange g).baseChange h).inclusion).left).obj
      (divisorLineBundle (pullSection h (pullSection g s) ≫
        ((E.baseChange g).baseChange h).inclusion).left.ker
        (smoothMarking_relativeCartier ((E.baseChange g).baseChange h)
          (pullSection h (pullSection g s))).1) ≅ structureModule U) :
    ∃ i : integralCurve (smoothMarkingWeierstrassCurve (F) (sF) b) ≅ integralCurve (W),
      i.hom ≫ integralCurveStructure (W) =
        integralCurveStructure (smoothMarkingWeierstrassCurve (F) (sF) b) ∧
      integralCurveZero (smoothMarkingWeierstrassCurve (F) (sF) b) ≫ i.hom =
        integralCurveZero (W) ∧
      smoothMarkingToIntegralCubic (F) (sF) b ≫ i.hom =
        (E.baseChangeCompIso g h).inv.curve.left ≫ smoothMarkingToIntegralCubic (D) (sD) a := by
  have hh := exists_smoothMarkingFamilyCubicIso (E.baseChangeCompIso g h) (sD) a
  rw [smoothMarkingAssociator_group] at hh
  exact hh b

end FLT.Mazur.GeneralizedEllipticCurve
