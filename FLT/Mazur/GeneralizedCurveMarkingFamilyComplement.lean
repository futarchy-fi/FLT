/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingFamilyPoles
public import FLT.Mazur.GeneralizedCurveMarkingComplementPullback

/-!
# Actual complement functions under an original family isomorphism

The inverse curve map restricts to the actual marking complements and retains
both base scalars and all transported pole functions. No affineness of the
whole marking complement is needed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback relativePoleFunction smoothMarkingFamilyLift
variable {S : Scheme} {E F : GeneralizedEllipticCurve S} (e : E ≅ F)
  (s : 𝟙_ (Over S) ⟶ E.group)
local instance markingFamilyComplementProper : IsProper E.curve.hom := E.family.family.1
local notation "t" => s ≫ E.inclusion
local notation "v" => (s ≫ e.hom.group) ≫ F.inclusion
local notation "hI" => And.left (smoothMarking_relativeCartier E s)
local notation "hJ" => And.left (smoothMarking_relativeCartier F (s ≫ e.hom.group))
local notation "H" => smoothMarkingIso_cartesian e
local notation "w" => smoothMarkingIso_sectionSquare e s

/-- The inverse family isomorphism restricts to the actual original marking complements. -/
def smoothMarkingFamilyComplementMap :
    Scheme.Opens.toScheme (X := F.curve.left) (v).left.ker.support.compl ⟶
      Scheme.Opens.toScheme (X := E.curve.left) (t).left.ker.support.compl :=
  sectionPointComplementMap (H) (t).left (v).left (t).w (v).w (w)

/-- The complement map is the restriction of the specified original family map. -/
@[reassoc] theorem smoothMarkingFamilyComplementMap_ι :
    smoothMarkingFamilyComplementMap e s ≫
      Scheme.Opens.ι (X := E.curve.left) (t).left.ker.support.compl =
        Scheme.Opens.ι (X := F.curve.left) (v).left.ker.support.compl ≫ e.inv.curve.left :=
  sectionPointComplementMap_ι (H) (t).left (v).left (t).w (v).w (w)

/-- Actual base scalars are unchanged by the family identification. -/
theorem smoothMarkingFamilyComplementMap_scalar (r : Γ(S, ⊤)) :
    (smoothMarkingFamilyComplementMap e s).appTop (smoothMarkingComplementBaseMap E s r) =
      smoothMarkingComplementBaseMap F (s ≫ e.hom.group) r := by
  unfold smoothMarkingComplementBaseMap smoothMarkingFamilyComplementMap
  have hh := sectionPointComplementMap_base (H) (t).left (v).left (t).w (v).w (w)
  rw [Category.comp_id] at hh
  have ha := congrArg Scheme.Hom.appTop hh
  simp only [Scheme.Hom.comp_appTop] at ha
  exact ConcreteCategory.congr_hom ha r

variable [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (a : (pullback (s ≫ E.inclusion).left).obj
    (divisorLineBundle (s ≫ E.inclusion).left.ker
      (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

/-- The actual regular function of every transported pole section is its original pullback. -/
theorem smoothMarkingFamilyComplementMap_lift (m : ℕ) (hm : 0 < m) :
    (smoothMarkingFamilyComplementMap e s).appTop
        (relativePoleFunction E.curve.hom (t).left (hI) (m + 1)
          (smoothMarkingFramedLift E s a m hm)) =
      relativePoleFunction F.curve.hom (v).left (hJ) (m + 1)
        (smoothMarkingFamilyLift e s a m hm) := by
  simpa only [smoothMarkingFamilyComplementMap, smoothMarkingFamilyLift] using
    sectionPointComplementMap_relativeFunction (H) (t).left (v).left
      (t).w (v).w (w) (hI) (hJ) m (smoothMarkingFramedLift E s a m hm)

end FLT.Mazur.GeneralizedEllipticCurve
