/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingFamilyIso
public import FLT.Mazur.GeneralizedCurveSectionComposition

/-!
# Original smooth markings under the canonical base-change associator

The associator identifies the actual group points, not only their whole-curve
images. Consequently its original Cartier ideal and every pole bound identify
the directly pulled family with the independently iterated family.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback
variable {S T U : Scheme} (E : GeneralizedEllipticCurve S)
  (g : T ⟶ S) (h : U ⟶ T) (s : 𝟙_ (Over S) ⟶ E.group)

/-- The canonical full-family associator retains the independently iterated smooth point. -/
theorem smoothMarkingAssociator_group :
    pullSection (h ≫ g) s ≫ (E.baseChangeCompIso g h).hom.group =
      pullSection h (pullSection g s) := by
  let F := (E.baseChange g).baseChange h
  let _ : Mono F.inclusion := by
    dsimp [GeneralizedEllipticCurve.inclusion, curveSmoothInclusion]
    infer_instance
  apply (cancel_mono F.inclusion).mp
  apply Over.OverMorphism.ext
  change ((pullSection (h ≫ g) s ≫
    (E.baseChangeCompIso g h).hom.group) ≫ F.inclusion).left = _
  erw [← smoothMarkingIso_section (E.baseChangeCompIso g h) (pullSection (h ≫ g) s)]
  rw [← pullSection_smoothMarking]
  rw [baseChangeCompIso_section]
  rw [pullSection_smoothMarking]
  exact congrArg Over.Hom.left (pullSection_smoothMarking (E.baseChange g) h (pullSection g s))

/-- The inverse associator pulls back the direct section ideal to the actual iterated ideal. -/
theorem smoothMarkingAssociator_ker :
    (pullSection (h ≫ g) s ≫ (E.baseChange (h ≫ g)).inclusion).left.ker.comap
        (E.baseChangeCompIso g h).inv.curve.left =
      (pullSection h (pullSection g s) ≫ ((E.baseChange g).baseChange h).inclusion).left.ker := by
  have hh := smoothMarkingIso_ker (E.baseChangeCompIso g h) (pullSection (h ≫ g) s)
  simpa only [← Category.assoc, smoothMarkingAssociator_group] using hh

/-- Every original pole power transports to the independently iterated family's pole power. -/
def smoothMarkingAssociatorPowerIso (m : ℕ) :
    (pullback (E.baseChangeCompIso g h).inv.curve.left).obj
      ((E.baseChange (h ≫ g)).smoothMarkingPower (pullSection (h ≫ g) s) m) ≅
        ((E.baseChange g).baseChange h).smoothMarkingPower
          (pullSection h (pullSection g s)) m := by
  simpa only [smoothMarkingAssociator_group] using
    smoothMarkingFamilyPowerIso (E.baseChangeCompIso g h) (pullSection (h ≫ g) s) m

end FLT.Mazur.GeneralizedEllipticCurve
