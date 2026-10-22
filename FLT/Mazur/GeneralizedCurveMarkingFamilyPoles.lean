/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingFamilyIso
public import FLT.Mazur.GeneralizedCurveMarkingTransportedFrame

/-!
# Original pole sections transported through a family isomorphism

The transported frame and sections use the actual inverse curve morphism.
Normalization is derived from the original Cartier square, allowing comparison
with independently chosen frames on the identified family.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback sectionPoleMultiplicativeCoordinates sectionPoleBaseChangeFrame
variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  {E F : GeneralizedEllipticCurve S} (e : E ≅ F) (s : 𝟙_ (Over S) ⟶ E.group)
local instance markingFamilyPolesProper : IsProper E.curve.hom := E.family.family.1
local instance markingFamilyPolesTargetProper : IsProper F.curve.hom := F.family.family.1
local notation "t" => s ≫ E.inclusion
local notation "v" => (s ≫ e.hom.group) ≫ F.inclusion
local notation "hI" => And.left (smoothMarking_relativeCartier E s)
local notation "hJ" => And.left (smoothMarking_relativeCartier F (s ≫ e.hom.group))
local notation "H" => smoothMarkingIso_cartesian e
local notation "w" => smoothMarkingIso_sectionSquare e s
variable (a : (pullback (s ≫ E.inclusion).left).obj
    (divisorLineBundle (s ≫ E.inclusion).left.ker
      (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

/-- The original line frame transported through the full family isomorphism. -/
def smoothMarkingFamilyFrame :
    (pullback (v).left).obj (divisorLineBundle (v).left.ker (hJ)) ≅ structureModule S :=
  sectionPointTransportedFrame (H) (t).left (v).left (t).w (v).w (w) (hI) (hJ) a

/-- The actual original pole lift transported to the identified family. -/
def smoothMarkingFamilyLift (m : ℕ) (hm : 0 < m) :
    ModuleRingH F.curve.hom.appTop.hom
      (tensorPower (divisorLineBundle (v).left.ker (hJ)) (m + 1)) 0 :=
  sectionPolePullH0 (H) (t).left (v).left (t).w (v).w (w) (hI) (hJ) m
    (smoothMarkingFramedLift E s a m hm)

/-- Transported pole sections are normalized in powers of one transported marking frame. -/
theorem smoothMarkingFamilyLift_coefficient (m : ℕ) (hm : 0 < m) :
    sectionPoleCoefficient (v).left (hJ) (smoothMarkingFamilyFrame e s a) (m + 1)
      (moduleH0Equiv _ (smoothMarkingFamilyLift e s a m hm)) = 1 := by
  have ha := smoothMarkingFramedLift_coefficient E s a m hm
  rw [sectionPoleCoefficient_leading (t).left (hI) a E.curve.hom (t).w] at ha
  rw [sectionPoleCoefficient_leading (v).left (hJ) _ F.curve.hom (v).w]
  unfold sectionPoleMultiplicativeCoordinates at ha ⊢
  have hh := sectionPoleBaseChangeFrame_normalized (H) (t).left (v).left
    (t).w (v).w (w) (hI) (hJ) m (sectionPoleMultiplicativeFrame (t).left (hI) a (m + 1))
    (smoothMarkingFramedLift E s a m hm) ha
  rw [sectionPoleBaseChangeFrame_multiplicative] at hh
  exact hh

end FLT.Mazur.GeneralizedEllipticCurve
