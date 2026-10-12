/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOnePointFibers
public import FLT.Mazur.ProperLinePushforwardLocalFree
public import FLT.Mazur.ProperLinePushforwardBaseChange

/-!
# Relative sections of positive point powers in genus-one group families

Actual fiber calculations produce acyclic positive point powers, finite
projective section modules, and finite free charts of the original direct
image. The canonical comparison commutes with every affine base change.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
open Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback LineSectionBaseChange Chow
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)
  (m : ℕ) (hm : 0 < m)

/-- Relative smoothness supplies flatness for cohomology and base change. -/
local instance relativePointSectionsSmooth : Smooth G.hom :=
  SmoothOfRelativeDimension.smooth 1 G.hom

include hg hm

omit [IsNoetherianRing Γ(S, ⊤)] in
/-- Residue-algebra fibers of the actual point power are acyclic. -/
theorem relative_pointPower_residue_acyclic (z : PrimeSpectrum Γ(S, ⊤)) (n : ℕ) :
    Subsingleton (ModuleH (residueAlgebraFiberLine G.hom
      (tensorPower (divisorLineBundle s.left.ker hI) m) z) (n + 1)) :=
  relative_pointPower_field_acyclic G hg s hI
    (AffineBaseChangeCoefficients.baseMap S z.asIdeal.ResidueField) m hm n

/-- Positive cohomology vanishes on the original varying family over its affine base. -/
theorem relative_pointPower_acyclic (n : ℕ) :
    Subsingleton (ModuleH (tensorPower (divisorLineBundle s.left.ker hI) m) (n + 1)) :=
  positive_vanishing_of_residue_fibers G.hom _
    (hI.divisorLineBundle_locallyFreeRankOne.tensorPower m)
    (relative_pointPower_residue_acyclic G hg s hI m hm) n

/-- The original point-power section module is finite projective over the base ring. -/
theorem relative_pointPower_sections_finite_projective :
    Module.Finite Γ(S, ⊤)
        (baseSections (tensorPower (divisorLineBundle s.left.ker hI) m) G.hom.appTop.hom ⊤) ∧
      Module.Projective Γ(S, ⊤)
        (baseSections (tensorPower (divisorLineBundle s.left.ker hI) m) G.hom.appTop.hom ⊤) := by
  let hL := hI.divisorLineBundle_locallyFreeRankOne.tensorPower m
  let _ := hL.isFinitePresentation
  exact ⟨proper_sections_finite G.hom _, projective_sections_of_residue_fibers G.hom _ hL
    (relative_pointPower_residue_acyclic G hg s hI m hm)⟩

/-- Genuine finite free charts exist for the original direct image. -/
theorem relative_pointPower_pushforward_locallyFiniteFree :
    LocallyFiniteFree ((pushforward G.hom).obj
      (tensorPower (divisorLineBundle s.left.ker hI) m)) :=
  properLinePushforward_locallyFiniteFree G.hom _
    (hI.divisorLineBundle_locallyFreeRankOne.tensorPower m)
    (relative_pointPower_residue_acyclic G hg s hI m hm)

omit hg hm in
/-- Canonical affine base change of the original point-power direct image. -/
def relativePointPowerPushforwardIso {P T : Scheme} [IsAffine T]
    {p : P ⟶ G.left} {q : P ⟶ T} {g : T ⟶ S} (h : IsPullback p q G.hom g) :
    (pullback g).obj ((pushforward G.hom).obj
      (tensorPower (divisorLineBundle s.left.ker hI) m)) ≅
        (pushforward q).obj ((pullback p).obj
          (tensorPower (divisorLineBundle s.left.ker hI) m)) :=
  properLinePushforwardBaseChangeIso h _
    (hI.divisorLineBundle_locallyFreeRankOne.tensorPower m)
    (relative_pointPower_residue_acyclic G hg s hI m hm)

end FLT.Mazur.FCurve
