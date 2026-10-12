/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneChangedBasis
public import FLT.Mazur.RelativeGenusOneCubicRelation
public import FLT.Mazur.SectionPointFrameBaseChange

/-!
# Actual changed families carry the constructed monomial basis

Transfer the underlying original line frame before taking its tensor powers.
The changed family's actual square, mixed product and cube then give its
order-six basis, with the original order-three square having cube coefficient one.
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
  (e : (pullback g).obj ((pullback s.left).obj (divisorLineBundle s.left.ker hI)) ≅
    structureModule T)

local notation "H" => Functor.obj (Over.pullback g) G
local notation "t" => pullSection g s
local notation "hJ" => changedPoint_cartier G s hI g

/-- The original frame transferred on the underlying line, before taking tensor powers. -/
def changedPointMonomialFrame :
    (pullback (t).left).obj (divisorLineBundle (t).left.ker hJ) ≅ structureModule T :=
  sectionPointChangedLineFrame (IsPullback.of_hasPullback G.hom g)
    s.left (t).left s.w (t).w (section_fst g s) hI hJ e

attribute [local irreducible] changedPointMonomialFrame

local instance changedMonomial_proper : IsProper (H).hom :=
  inferInstanceAs (IsProper (Limits.pullback.snd G.hom g))

local instance changedMonomial_smooth : SmoothOfRelativeDimension 1 (H).hom :=
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback G.hom g)
    (inferInstance : SmoothOfRelativeDimension 1 G.hom)

local instance changedMonomial_integral : GeometricallyIntegral (H).hom :=
  inferInstanceAs (GeometricallyIntegral (Limits.pullback.snd G.hom g))

/-- The six-vector basis on the actual changed family, using its actual pole products. -/
def changedPointMonomialSixBasis :
    Basis (((((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) Γ(T, ⊤)
      (ModuleRingH (H).hom.appTop.hom (tensorPower (divisorLineBundle (t).left.ker hJ) 6) 0) :=
  relativePointMonomialSixBasis H (hg.baseChange g) t hJ (changedPointMonomialFrame G s hI g e)

/-- The final vector of the changed-family basis is the cube of its original order-two lift. -/
theorem changedPointMonomialSixBasis_new :
    changedPointMonomialSixBasis G hg s hI g e (Sum.inr ()) =
      relativePointFramedCube H (hg.baseChange g) t hJ (changedPointMonomialFrame G s hI g e) :=
  relativePointMonomialSixBasis_new H (hg.baseChange g) t hJ _

/-- The actual order-three square has unit cube coefficient after change of base. -/
theorem changedPointMonomialSixBasis_YSquare_last :
    (changedPointMonomialSixBasis G hg s hI g e).repr
      (relativePointFramedYSquare H (hg.baseChange g) t hJ
        (changedPointMonomialFrame G s hI g e)) (Sum.inr ()) = 1 :=
  relativePointMonomialSixBasis_YSquare_last H (hg.baseChange g) t hJ _

end FLT.Mazur.FCurve
