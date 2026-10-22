/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionPoleBaseChangeDifference
public import FLT.Mazur.GeneralizedCurveMarkingFramedProducts
public import FLT.Mazur.GeneralizedCurveMarkingBaseChange

/-!
# Independently recomputed pole lifts on the actual changed family

The new family's chosen lift and the transported original chosen lift have
an exact unit scaling and a unique lower-pole correction. The normalization
of both lifts is proved from their construction, not supplied as a hypothesis.
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

local instance generalizedCurveMarkingTransportedLiftProper :
    IsProper E.curve.hom := E.family.family.1

local instance generalizedCurveMarkingTransportedLiftChangedProper :
    IsProper (E.baseChange g).curve.hom := (E.baseChange g).family.family.1

omit [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [IsAffine T] [IsNoetherianRing Γ(T, ⊤)] in
/-- The retained marking commutes with the original total-space projection. -/
theorem smoothMarkingBaseChange_sectionSquare :
    (pullSection g s ≫ (E.baseChange g).inclusion).left ≫
      Limits.pullback.fst E.curve.hom g = g ≫ (s ≫ E.inclusion).left := by
  rw [← pullSection_smoothMarking]
  exact section_fst g (s ≫ E.inclusion)

omit [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [IsAffine T] [IsNoetherianRing Γ(T, ⊤)] in
/-- The original pullback square with the changed family's named structure morphism. -/
theorem smoothMarkingBaseChange_cartesian :
    IsPullback (Limits.pullback.fst E.curve.hom g) (E.baseChange g).curve.hom
      E.curve.hom g := IsPullback.of_hasPullback E.curve.hom g

variable (a : (pullback (s ≫ E.inclusion).left).obj
    (divisorLineBundle (s ≫ E.inclusion).left.ker
      (smoothMarking_relativeCartier E s).1) ≅ structureModule S)
  (b : (pullback (pullSection g s ≫ (E.baseChange g).inclusion).left).obj
    (divisorLineBundle (pullSection g s ≫ (E.baseChange g).inclusion).left.ker
      (smoothMarking_relativeCartier (E.baseChange g) (pullSection g s)).1) ≅ structureModule T)
local notation "t" => s ≫ E.inclusion
local notation "v" => pullSection g s ≫ GeneralizedEllipticCurve.inclusion (E.baseChange g)
local notation "hI" => And.left (smoothMarking_relativeCartier E s)
local notation "hJ" => And.left (smoothMarking_relativeCartier (E.baseChange g) (pullSection g s))
local notation "H" => smoothMarkingBaseChange_cartesian E g
local notation "w" => smoothMarkingBaseChange_sectionSquare E g s

/-- Independently chosen lifts on the changed family retain their unique lower-pole defect. -/
theorem smoothMarkingFramedLift_baseChange_difference (m : ℕ) (hm : 0 < m) :
    ∃! z : ModuleRingH (E.baseChange g).curve.hom.appTop.hom
        (tensorPower (divisorLineBundle (v).left.ker (hJ)) m) 0,
      smoothMarkingFramedLift (E.baseChange g) (pullSection g s) b m hm =
        (frameComparisonUnit
          (sectionPoleBaseChangeFrame (H) (t).left (v).left (t).w (v).w (w) (hI) (hJ)
            (m + 1) (sectionPoleMultiplicativeFrame (t).left (hI) a (m + 1)))
          (sectionPoleMultiplicativeFrame (v).left (hJ) b (m + 1)) ⊤ : Γ(T, ⊤)) •
        sectionPolePullH0 (H) (t).left (v).left (t).w (v).w (w) (hI) (hJ) m
          (smoothMarkingFramedLift E s a m hm) +
        divisorPowerRingStep (E.baseChange g).curve.hom.appTop.hom (hJ) m z := by
  have ha := smoothMarkingFramedLift_coefficient E s a m hm
  have hb := smoothMarkingFramedLift_coefficient (E.baseChange g) (pullSection g s) b m hm
  rw [sectionPoleCoefficient_leading (t).left (hI) a E.curve.hom (t).w] at ha
  rw [sectionPoleCoefficient_leading (v).left (hJ) b (E.baseChange g).curve.hom (v).w] at hb
  unfold sectionPoleMultiplicativeCoordinates at ha hb
  exact sectionPoleBaseChangeFrameDifference_existsUnique (H) (t).left (v).left
    (t).w (v).w (w) (hI) (hJ) m
    (sectionPoleMultiplicativeFrame (t).left (hI) a (m + 1))
    (smoothMarkingFramedLift E s a m hm)
    (smoothMarkingFramedLift (E.baseChange g) (pullSection g s) b m hm)
    (sectionPoleMultiplicativeFrame (v).left (hJ) b (m + 1)) ha hb

end FLT.Mazur.GeneralizedEllipticCurve
