/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NodalGenusOneBaseChange
public import FLT.Mazur.RelativeGenusOneLowPoleBasis
public import FLT.Mazur.SectionPoleBaseChangeFrames

/-!
# Low pole bases on the actual changed genus-one family

The group, smoothness, integrality and genus hypotheses descend to the actual
fiber product. A single pulled original frame supplies both leading coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory Module
open scoped CategoryTheory.Obj
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle

variable {S T : Scheme} [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker) (g : T ⟶ S)

local notation "H" => Functor.obj (Over.pullback g) G
local notation "t" => pullSection g s

omit [IsAffine T] [IsNoetherianRing Γ(T, ⊤)] [GrpObj G]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom] in
include hI in
/-- The actual retained group section has a Cartier ideal on the fiber product. -/
theorem changedPoint_cartier : EffectiveCartier (t).left.ker :=
  sectionPoint_cartier_baseChange (IsPullback.of_hasPullback G.hom g)
    s.left (t).left s.w (t).w (section_fst g s) hI

local notation "hJ" => changedPoint_cartier G s hI g

/-- Leading coordinates in all degrees come from one frame of the original line. -/
def changedPointCoordinates
    (e : (pullback g).obj ((pullback s.left).obj (divisorLineBundle s.left.ker hI)) ≅
      structureModule T) (m : ℕ) :
    Γ(sectionPoleLine (t).left hJ m, ⊤) ≃ₗ[Γ(T, ⊤)] Γ(T, ⊤) :=
  sectionPoleChangedCoordinates (IsPullback.of_hasPullback G.hom g)
    s.left (t).left s.w (t).w (section_fst g s) hI hJ e m

attribute [local irreducible] changedPointCoordinates

local instance changedPoint_proper : IsProper (H).hom :=
  inferInstanceAs (IsProper (Limits.pullback.snd G.hom g))

local instance changedPoint_smooth : SmoothOfRelativeDimension 1 (H).hom :=
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback G.hom g)
    (inferInstance : SmoothOfRelativeDimension 1 G.hom)

local instance changedPoint_integral : GeometricallyIntegral (H).hom :=
  inferInstanceAs (GeometricallyIntegral (Limits.pullback.snd G.hom g))

/-- The normalized order-two basis on the actual changed total space. -/
def changedPointTwoBasis
    (e : (pullback g).obj ((pullback s.left).obj (divisorLineBundle s.left.ker hI)) ≅
      structureModule T) :
    Basis (Unit ⊕ Unit) Γ(T, ⊤)
      (ModuleRingH (H).hom.appTop.hom (tensorPower (divisorLineBundle (t).left.ker hJ) 2) 0) :=
  relativePointTwoBasis H (hg.baseChange g) t hJ (changedPointCoordinates G s hI g e 2)

/-- The compatible order-three basis uses the same original frame as order two. -/
def changedPointThreeBasis
    (e : (pullback g).obj ((pullback s.left).obj (divisorLineBundle s.left.ker hI)) ≅
      structureModule T) :
    Basis ((Unit ⊕ Unit) ⊕ Unit) Γ(T, ⊤)
      (ModuleRingH (H).hom.appTop.hom (tensorPower (divisorLineBundle (t).left.ker hJ) 3) 0) :=
  relativePointThreeBasis H (hg.baseChange g) t hJ
    (changedPointCoordinates G s hI g e 2) (changedPointCoordinates G s hI g e 3)

/-- Original divisor transitions embed the order-two basis in the order-three basis. -/
theorem changedPointThreeBasis_old
    (e : (pullback g).obj ((pullback s.left).obj (divisorLineBundle s.left.ker hI)) ≅
      structureModule T) (i : Unit ⊕ Unit) :
    changedPointThreeBasis G hg s hI g e (Sum.inl i) =
      divisorPowerRingStep (H).hom.appTop.hom hJ 2 (changedPointTwoBasis G hg s hI g e i) :=
  relativePointThreeBasis_old H (hg.baseChange g) t hJ _ _ i

/-- The new order-two vector has leading coefficient one in the transferred frame. -/
theorem changedPointTwoBasis_leading
    (e : (pullback g).obj ((pullback s.left).obj (divisorLineBundle s.left.ker hI)) ≅
      structureModule T) :
    changedPointCoordinates G s hI g e 2
      (sectionPoleLeading (H).hom (t).left (t).w hJ 1
        (changedPointTwoBasis G hg s hI g e (Sum.inr ()))) = 1 := by
  change changedPointCoordinates G s hI g e 2
    (sectionPoleLeading (H).hom (t).left (t).w hJ 1
      (relativePointTwoBasis H (hg.baseChange g) t hJ _ (Sum.inr ()))) = 1
  rw [relativePointTwoBasis_new]
  exact relativePointNormalizedLift_leading H (hg.baseChange g) t hJ 1 (by decide) _

/-- The new order-three vector has leading coefficient one from that same frame. -/
theorem changedPointThreeBasis_leading
    (e : (pullback g).obj ((pullback s.left).obj (divisorLineBundle s.left.ker hI)) ≅
      structureModule T) :
    changedPointCoordinates G s hI g e 3
      (sectionPoleLeading (H).hom (t).left (t).w hJ 2
        (changedPointThreeBasis G hg s hI g e (Sum.inr ()))) = 1 := by
  change changedPointCoordinates G s hI g e 3
    (sectionPoleLeading (H).hom (t).left (t).w hJ 2
      (relativePointThreeBasis H (hg.baseChange g) t hJ _ _ (Sum.inr ()))) = 1
  rw [relativePointThreeBasis_new]
  exact relativePointNormalizedLift_leading H (hg.baseChange g) t hJ 2 (by decide) _

end FLT.Mazur.FCurve
