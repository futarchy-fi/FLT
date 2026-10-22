/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingTransportedLift
public import FLT.Mazur.SectionPoleTransportedMultiplicativeFrame

/-!
# One transported marking frame for the actual changed curve

The original marking frame determines all transported leading frames.
Independently recomputed pole lifts therefore have powers of one common
transition unit, with their unique lower-pole corrections retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback sectionPoleMultiplicativeCoordinates sectionPoleBaseChangeFrame
variable {S T : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]
  (E : GeneralizedEllipticCurve S) (g : T ⟶ S) (s : 𝟙_ (Over S) ⟶ E.group)

local instance generalizedCurveMarkingTransportedFrameProper :
    IsProper E.curve.hom := E.family.family.1

local instance generalizedCurveMarkingTransportedFrameChangedProper :
    IsProper (E.baseChange g).curve.hom := (E.baseChange g).family.family.1

variable (a : (pullback (s ≫ E.inclusion).left).obj
    (divisorLineBundle (s ≫ E.inclusion).left.ker
      (smoothMarking_relativeCartier E s).1) ≅ structureModule S)
local notation "t" => s ≫ E.inclusion
local notation "v" => pullSection g s ≫ GeneralizedEllipticCurve.inclusion (E.baseChange g)
local notation "hI" => And.left (smoothMarking_relativeCartier E s)
local notation "hJ" => And.left (smoothMarking_relativeCartier (E.baseChange g) (pullSection g s))
local notation "H" => smoothMarkingBaseChange_cartesian E g
local notation "w" => smoothMarkingBaseChange_sectionSquare E g s

/-- The original frame transported to the actual new marked line. -/
def smoothMarkingTransportedFrame :
    (pullback (v).left).obj (divisorLineBundle (v).left.ker (hJ)) ≅ structureModule T :=
  sectionPointTransportedFrame (H) (t).left (v).left (t).w (v).w (w) (hI) (hJ) a

/-- Transport of the original chosen lift with the actual new base-ring module. -/
def smoothMarkingTransportedLift (m : ℕ) (hm : 0 < m) :
    ModuleRingH (E.baseChange g).curve.hom.appTop.hom
      (tensorPower (divisorLineBundle (v).left.ker (hJ)) (m + 1)) 0 :=
  sectionPolePullH0 (H) (t).left (v).left (t).w (v).w (w) (hI) (hJ) m
    (smoothMarkingFramedLift E s a m hm)

omit [IsAffine T] [IsNoetherianRing Γ(T, ⊤)] in
/-- The transported actual section is normalized in the transported multiplicative frame. -/
theorem smoothMarkingTransportedLift_coefficient (m : ℕ) (hm : 0 < m) :
    sectionPoleCoefficient (v).left (hJ) (smoothMarkingTransportedFrame E g s a) (m + 1)
      (moduleH0Equiv _ (smoothMarkingTransportedLift E g s a m hm)) = 1 := by
  have ha := smoothMarkingFramedLift_coefficient E s a m hm
  rw [sectionPoleCoefficient_leading (t).left (hI) a E.curve.hom (t).w] at ha
  rw [sectionPoleCoefficient_leading (v).left (hJ) _ (E.baseChange g).curve.hom (v).w]
  unfold sectionPoleMultiplicativeCoordinates at ha ⊢
  have hh := sectionPoleBaseChangeFrame_normalized (H) (t).left (v).left
    (t).w (v).w (w) (hI) (hJ) m (sectionPoleMultiplicativeFrame (t).left (hI) a (m + 1))
    (smoothMarkingFramedLift E s a m hm) ha
  rw [sectionPoleBaseChangeFrame_multiplicative] at hh
  exact hh

attribute [local irreducible] smoothMarkingTransportedFrame smoothMarkingTransportedLift

/-- All independent pole-lift differences use powers of the same original line transition. -/
theorem smoothMarkingTransportedLift_difference
    (b : (pullback (pullSection g s ≫ (E.baseChange g).inclusion).left).obj
      (divisorLineBundle (pullSection g s ≫ (E.baseChange g).inclusion).left.ker
        (smoothMarking_relativeCartier (E.baseChange g) (pullSection g s)).1) ≅ structureModule T)
    (m : ℕ) (hm : 0 < m) :
    ∃! z : ModuleRingH (E.baseChange g).curve.hom.appTop.hom
        (tensorPower (divisorLineBundle (v).left.ker (hJ)) m) 0,
      smoothMarkingFramedLift (E.baseChange g) (pullSection g s) b m hm =
        (frameComparisonUnit (X := T) (smoothMarkingTransportedFrame E g s a) b ⊤ : Γ(T, ⊤)) ^
          (m + 1) • smoothMarkingTransportedLift E g s a m hm +
        divisorPowerRingStep (E.baseChange g).curve.hom.appTop.hom (hJ) m z := by
  have hh := smoothMarkingFramedLift_baseChange_difference E g s a b m hm
  rw [sectionPoleBaseChangeFrame_unit, Units.val_pow_eq_pow_val] at hh
  simpa only [smoothMarkingTransportedFrame, smoothMarkingTransportedLift] using hh

end FLT.Mazur.GeneralizedEllipticCurve
