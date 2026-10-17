/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFrameTestSplitting
public import FLT.Mazur.UniversallyClosedFiniteCover
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Finiteness of whole original pullbacks over complete tests

A complete frame splits the entire pullback, so its projection is finite.
The test may be nonreduced or closed in the frame space; no extension to an
ambient open is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] distinctScheme completeTestIso testComparison testSection
variable {S : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (I : Type) [Fintype I] {T : Scheme} {b : T ⟶ S}
  (t : Over.mk b ⟶ distinctScheme E I)

/-- Complete tests make the whole original projection finite, including all nilpotents. -/
theorem finite_pullback_of_complete (ht : Set.range t.left ⊆ completeLocus E I) :
    IsFinite (pullback.snd E.hom b) := by
  let a := completeTestIso E I t ht
  let g := a.hom ≫ pullback.snd E.hom b
  have hg (i : I) : Sigma.ι (fun _ : I ↦ T) i ≫ g = 𝟙 T := by
    dsimp only [g]
    rw [completeTestIso_component_assoc, testSection_snd]
  have hU (i : I) :
      UniversallyClosed ((sigmaOpenCover (fun _ : I ↦ T)).f i ≫ g) := by
    change UniversallyClosed (Sigma.ι (fun _ : I ↦ T) i ≫ g)
    rw [hg]
    infer_instance
  let _ : Finite (sigmaOpenCover (fun _ : I ↦ T)).I₀ := inferInstanceAs (Finite I)
  let _ : UniversallyClosed g :=
    UniversallyClosedFiniteCover.universallyClosed g (sigmaOpenCover _) hU
  let _ : UniversallyClosed (pullback.snd E.hom b) :=
    UniversallyClosed.of_comp_surjective a.hom (pullback.snd E.hom b)
  let _ : IsProper (pullback.snd E.hom b) := ⟨⟩
  let _ : LocallyQuasiFinite (pullback.snd E.hom b) :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ (fun y ↦ by
      apply (Set.finite_range (fun i ↦ testSection E I t i y)).subset
      intro z hz
      obtain ⟨i, x, rfl⟩ := testSection_cover_of_complete E I t ht z
      have hx : x = y := by
        have hs := congrArg (fun h : T ⟶ T ↦ h x) (testSection_snd E I t i)
        exact hs.symm.trans hz
      exact ⟨i, congrArg (testSection E I t i) hx.symm⟩)
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

end FLT.Mazur.RelativeOrderedTuples
