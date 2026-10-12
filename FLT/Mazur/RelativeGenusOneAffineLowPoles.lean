/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneChangedBasis

/-!
# Affine neighborhoods with normalized original low-pole bases

Every base point has one affine neighborhood on which the retained family
has compatible order-two and order-three bases with prescribed unit leading terms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory Module
open scoped CategoryTheory.Obj
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle changedPointCoordinates

variable {S : Scheme} [IsLocallyNoetherian S]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)

include hg in
/-- One actual affine restriction carries both low-pole bases and their original transitions. -/
theorem relativePoint_affine_lowPoleBases (x : S) :
    ∃ U : S.Opens, x ∈ U ∧ IsAffineOpen U ∧
      ∃ e : (pullback U.ι).obj ((pullback s.left).obj (divisorLineBundle s.left.ker hI)) ≅
          structureModule U.toScheme,
        let H := (Over.pullback U.ι).obj G
        let _ : IsProper H.hom := inferInstanceAs (IsProper (Limits.pullback.snd G.hom U.ι))
        let t := pullSection U.ι s
        let hJ := changedPoint_cartier G s hI U.ι
        ∃ b₂ : Basis (Unit ⊕ Unit) Γ(U.toScheme, ⊤)
            (ModuleRingH H.hom.appTop.hom (tensorPower (divisorLineBundle t.left.ker hJ) 2) 0),
          ∃ b₃ : Basis ((Unit ⊕ Unit) ⊕ Unit) Γ(U.toScheme, ⊤)
              (ModuleRingH H.hom.appTop.hom
                (tensorPower (divisorLineBundle t.left.ker hJ) 3) 0),
            (∀ i, b₃ (Sum.inl i) = divisorPowerRingStep H.hom.appTop.hom hJ 2 (b₂ i)) ∧
            changedPointCoordinates G s hI U.ι e 2
              (sectionPoleLeading H.hom t.left t.w hJ 1 (b₂ (Sum.inr ()))) = 1 ∧
            changedPointCoordinates G s hI U.ι e 3
              (sectionPoleLeading H.hom t.left t.w hJ 2 (b₃ (Sum.inr ()))) = 1 := by
  obtain ⟨U, hx, hU, ⟨e⟩⟩ := sectionPoleLine_affine_frame (S := S) s.left hI x
  let _ : IsAffine U.toScheme := hU
  let _ : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  let _ : IsNoetherianRing Γ(U.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top U.toScheme⟩
  let e' := ((restrictFunctorIsoPullback U.ι).app _).symm ≪≫ e
  refine ⟨U, hx, hU, e', changedPointTwoBasis G hg s hI U.ι e',
    changedPointThreeBasis G hg s hI U.ι e', ?_, ?_, ?_⟩
  · exact changedPointThreeBasis_old G hg s hI U.ι e'
  · exact changedPointTwoBasis_leading G hg s hI U.ι e'
  · exact changedPointThreeBasis_leading G hg s hI U.ι e'

end FLT.Mazur.FCurve
