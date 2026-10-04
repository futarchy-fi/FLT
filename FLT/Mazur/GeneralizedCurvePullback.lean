/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveCategory

/-!
# Pullback of the curve, group and action

Arbitrary scheme base change preserves the classified genus-one family,
commutative group, action laws, multiplication restriction and morphisms.
These statements concern the actual pullback objects. Identification with the
new relative smooth open and preservation of the geometric graph are separate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.GeneralizedEllipticCurve
variable {S T : Scheme} (E : GeneralizedEllipticCurve S) (g : T ⟶ S)

/-- The actual base-changed curve. -/
abbrev pullbackCurve : Over T := (Over.pullback g).obj E.curve
/-- The actual base-changed commutative group. -/
abbrev pullbackGroup : Over T := (Over.pullback g).obj E.group
/-- The actual base-changed inclusion. -/
def pullbackInclusion : E.pullbackGroup g ⟶ E.pullbackCurve g :=
  (Over.pullback g).map E.inclusion
/-- The action transported by the monoidal pullback functor. -/
def pullbackAction : E.pullbackGroup g ⊗ E.pullbackCurve g ⟶ E.pullbackCurve g :=
  Functor.LaxMonoidal.μ (Over.pullback g) E.group E.curve ≫ (Over.pullback g).map E.act

/-- The family conditions hold after arbitrary scheme base change. -/
theorem pullback_family : FCurve.ClassifiedGenusOneFamily (E.pullbackCurve g).hom :=
  E.family.baseChange g

/-- The pulled-back identity acts trivially. -/
theorem pullback_unit : η[E.pullbackGroup g] ▷ E.pullbackCurve g ≫ E.pullbackAction g =
    (λ_ (E.pullbackCurve g)).hom :=
  MonoidalActionMap.map_unit (Over.pullback g) E.act E.unit_act

/-- The pulled-back multiplication acts associatively. -/
theorem pullback_assoc : μ[E.pullbackGroup g] ▷ E.pullbackCurve g ≫ E.pullbackAction g =
    (α_ (E.pullbackGroup g) (E.pullbackGroup g) (E.pullbackCurve g)).hom ≫
      E.pullbackGroup g ◁ E.pullbackAction g ≫ E.pullbackAction g :=
  MonoidalActionMap.map_assoc (Over.pullback g) E.act E.assoc_act

/-- Restriction of the pulled-back action is the pulled-back multiplication. -/
theorem pullback_restriction :
    E.pullbackGroup g ◁ E.pullbackInclusion g ≫ E.pullbackAction g =
      μ[E.pullbackGroup g] ≫ E.pullbackInclusion g := by
  dsimp [pullbackAction, pullbackInclusion]
  rw [Functor.LaxMonoidal.μ_natural_right_assoc, ← Functor.map_comp, E.action_inclusion]
  simp only [Functor.map_comp, Category.assoc]

variable {E} {F : GeneralizedEllipticCurve S}

/-- Equivariance persists for the actual maps on both pullbacks. -/
theorem pullback_map_action (f : E ⟶ F) :
    E.pullbackAction g ≫ (Over.pullback g).map f.curve =
      ((Over.pullback g).map f.group ⊗ₘ (Over.pullback g).map f.curve) ≫
        F.pullbackAction g := by
  dsimp [pullbackAction]
  rw [Category.assoc, ← Functor.map_comp, f.action, Functor.map_comp,
    Functor.LaxMonoidal.μ_natural_assoc]

/-- Compatibility with the group inclusion persists under pullback. -/
theorem pullback_map_inclusion (f : E ⟶ F) :
    E.pullbackInclusion g ≫ (Over.pullback g).map f.curve =
      (Over.pullback g).map f.group ≫ F.pullbackInclusion g := by
  simp only [pullbackInclusion, ← Functor.map_comp, f.inclusion]

/-- Curve pullback is functorial on compatible generalized-curve morphisms. -/
def pullbackCurveFunctor : GeneralizedEllipticCurve S ⥤ Over T :=
  forgetCurve ⋙ Over.pullback g

/-- Group pullback is functorial on compatible generalized-curve morphisms. -/
def pullbackGroupFunctor : GeneralizedEllipticCurve S ⥤ Over T :=
  forgetGroup ⋙ Over.pullback g

end FLT.Mazur.GeneralizedEllipticCurve
