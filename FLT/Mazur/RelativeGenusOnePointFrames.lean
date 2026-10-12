/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOnePointSections
public import FLT.Mazur.FiniteProjectiveRankFrames
public import FLT.Mazur.ProperLineRankOneCohomology

/-!
# Exact-rank frames for the original relative pole spaces

Residue-field cohomology computes the rank of the actual section module.
Finite projectivity then constructs local frames of exactly m sections for
O(ms), including the pole orders two, three and six used for coordinates.
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
local instance relativePointFramesSmooth : Smooth G.hom :=
  SmoothOfRelativeDimension.smooth 1 G.hom

include hg hm

/-- The actual relative pole module has rank exactly m at every base point. -/
theorem relative_pointPower_section_rank (x : S) :
    Module.rankAtStalk (R := Γ(S, ⊤))
      (baseSections (tensorPower (divisorLineBundle s.left.ker hI) m) G.hom.appTop.hom ⊤)
      (S.isoSpec.hom x) = m := by
  let g := S.fromSpecResidueField x
  have h := properLineSectionRank_fieldFiber G.hom _
    (hI.divisorLineBundle_locallyFreeRankOne.tensorPower m)
    (relative_pointPower_residue_acyclic G hg s hI m hm)
    (IsPullback.of_hasPullback G.hom g) (IsLocalRing.closedPoint (S.residueField x))
  have hd := relative_pointPower_field_h0 G hg s hI g m hm
  have hx : g (IsLocalRing.closedPoint (S.residueField x)) = x :=
    S.fromSpecResidueField_apply x _
  exact (congrArg (fun y : S ↦ Module.rankAtStalk (R := Γ(S, ⊤))
    (baseSections (tensorPower (divisorLineBundle s.left.ker hI) m) G.hom.appTop.hom ⊤)
      (S.isoSpec.hom y)) hx).symm.trans (h.trans hd)

/-- The original direct image admits actual local frames with exactly m entries. -/
theorem relative_pointPower_frame (x : S) :
    ∃ U : S.Opens, x ∈ U ∧ Nonempty
      (((pushforward G.hom).obj (tensorPower (divisorLineBundle s.left.ker hI) m)).restrict U.ι
        ≅ SheafOfModules.free (Fin m)) := by
  let L := tensorPower (divisorLineBundle s.left.ker hI) m
  let _ := (hI.divisorLineBundle_locallyFreeRankOne.tensorPower m).isFinitePresentation
  obtain ⟨hf, hp⟩ := relative_pointPower_sections_finite_projective G hg s hI m hm
  let _ := hf
  let _ := hp
  let M := ModuleCat.of Γ(S, ⊤) (baseSections L G.hom.appTop.hom ⊤)
  obtain ⟨U, hx, ⟨e⟩⟩ := finiteProjective_rank_pullback_frame M S.isoSpec.hom m x
    (relative_pointPower_section_rank G hg s hI m hm x)
  exact ⟨U, hx, ⟨((restrictFunctor U.ι).mapIso
    (properPushforwardTildeIso G.hom L)).symm ≪≫ e⟩⟩

end FLT.Mazur.FCurve
