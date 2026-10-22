/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveCategory
public import FLT.Mazur.GeneralizedCurveMarkingBaseChange

/-!
# The original marking and its line under a family isomorphism

An isomorphism of generalized curves transports the actual smooth marking.
Its inverse gives a cartesian square over the identity base map, so the
original Cartier line and every pole power transport without flatness assumptions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback
variable {S : Scheme} {E F : GeneralizedEllipticCurve S} (e : E ≅ F)
  (s : 𝟙_ (Over S) ⟶ E.group)

/-- A family isomorphism carries the original whole-curve marking to its transported point. -/
@[reassoc] theorem smoothMarkingIso_section :
    (s ≫ E.inclusion).left ≫ e.hom.curve.left =
      ((s ≫ e.hom.group) ≫ F.inclusion).left := by
  change ((s ≫ E.inclusion) ≫ e.hom.curve).left = _
  rw [Category.assoc, e.hom.inclusion, ← Category.assoc]

/-- The inverse family map retains the original marking square over the identity base. -/
theorem smoothMarkingIso_sectionSquare :
    ((s ≫ e.hom.group) ≫ F.inclusion).left ≫ e.inv.curve.left =
      𝟙 S ≫ (s ≫ E.inclusion).left := by
  rw [← smoothMarkingIso_section, Category.assoc]
  have hi := ((forgetCurve ⋙ Over.forget S).mapIso e).hom_inv_id
  change e.hom.curve.left ≫ e.inv.curve.left = 𝟙 _ at hi
  rw [hi, Category.comp_id, Category.id_comp]

/-- The actual inverse curve isomorphism is a cartesian morphism over the fixed base. -/
theorem smoothMarkingIso_cartesian :
    IsPullback e.inv.curve.left F.curve.hom E.curve.hom (𝟙 S) := by
  let i := ((forgetCurve ⋙ Over.forget S).mapIso e).symm
  change IsPullback i.hom _ _ _
  apply IsPullback.of_horiz_isIso
  exact ⟨e.inv.curve.w.trans (Category.comp_id _).symm⟩

local instance markingFamilyIsoProper : IsProper E.curve.hom := E.family.family.1
local notation "t" => s ≫ E.inclusion
local notation "v" => (s ≫ e.hom.group) ≫ F.inclusion
local notation "hI" => And.left (smoothMarking_relativeCartier E s)
local notation "hJ" => And.left (smoothMarking_relativeCartier F (s ≫ e.hom.group))

/-- The original marking ideal pulls back to the transported marking ideal. -/
theorem smoothMarkingIso_ker :
    (t).left.ker.comap e.inv.curve.left = (v).left.ker :=
  section_ker_comap_of_cartesian (smoothMarkingIso_cartesian e)
    (v).left (t).left (v).w (t).w (smoothMarkingIso_sectionSquare e s)

/-- The original Cartier line is identified with the transported marking line. -/
irreducible_def smoothMarkingFamilyLineIso :
    (pullback e.inv.curve.left).obj (divisorLineBundle (t).left.ker (hI)) ≅
      divisorLineBundle (v).left.ker (hJ) :=
  sectionPointLineIso (smoothMarkingIso_cartesian e) (t).left (v).left
    (t).w (v).w (smoothMarkingIso_sectionSquare e s) (hI) (hJ)

/-- The canonical point-line comparison retains the section vanishing at the marking. -/
theorem smoothMarkingFamilyLineIso_section :
    (pullback e.inv.curve.left).map (divisorSectionMap (hI)) ≫
      (sectionPointLineIso (smoothMarkingIso_cartesian e) (t).left (v).left
        (t).w (v).w (smoothMarkingIso_sectionSquare e s) (hI) (hJ)).hom =
      (modulePullbackUnitIso e.inv.curve.left).hom ≫ divisorSectionMap (hJ) :=
  sectionPointLineIso_section (smoothMarkingIso_cartesian e) (t).left (v).left
    (t).w (v).w (smoothMarkingIso_sectionSquare e s) (hI) (hJ)

/-- Every pole bound transports along the original family isomorphism. -/
def smoothMarkingFamilyPowerIso (m : ℕ) :
    (pullback e.inv.curve.left).obj (E.smoothMarkingPower s m) ≅
      F.smoothMarkingPower (s ≫ e.hom.group) m :=
  sectionPointPowerIso (smoothMarkingIso_cartesian e) (t).left (v).left
    (t).w (v).w (smoothMarkingIso_sectionSquare e s) (hI) (hJ) m

end FLT.Mazur.GeneralizedEllipticCurve
