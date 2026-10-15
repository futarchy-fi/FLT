/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartesianNormFullFiber
public import FLT.Mazur.AffineHilbertTranslationAdmissibilityDetection

/-!
# Full fibers detected by jointly covering translation subcharts

The members of a translation cover need not be Cartesian over the old ground.
Their entire envelope fibers jointly detect the original full-fiber domain.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeOpenEnvelope
universe u v
variable {X Y : Scheme.{u}} (π : Y ⟶ X)
  {I : Type v} (E : I → Scheme.{u}) (g : ∀ i, E i ⟶ Y)
  (hg : ∀ y : Y, ∃ i, ∃ z : E i, g i z = y) (U : Y.Opens)

include hg

/-- Joint coverage, rather than Cartesianity of each chart, tests the whole fiber. -/
theorem fullFiberLocus_jointCover :
    fullFiberLocus π U = ⋂ i, fullFiberLocus (g i ≫ π) (g i ⁻¹ᵁ U) := by
  ext x
  simp only [Set.mem_iInter, mem_fullFiberLocus]
  constructor
  · intro h i z hz
    exact h (g i z) hz
  · intro h y hy
    obtain ⟨i, z, rfl⟩ := hg y
    exact h i z hy

end FLT.Mazur.SchemeOpenEnvelope

namespace FLT.Mazur.SchemeTranslationNorm
universe v
variable {R : Type} [CommRing R] (B W : Over (Spec (.of R)))
  {I : Type v} (T : I → Over (Spec (.of R))) (t : ∀ i, T i ⟶ W)
  (ht : ∀ w : W.left, ∃ i, ∃ z : (T i).left, (t i).left z = w)

include ht

/-- Product base change preserves joint coverage, with every residue-field branch retained. -/
theorem translationEnvelope_jointCover (y : (prod B W).left) :
    ∃ i, ∃ z : (prod B (T i)).left, (prod.map (𝟙 B) (t i)).left z = y := by
  obtain ⟨i, w, hw⟩ := ht ((prod.snd : prod B W ⟶ W).left y)
  have H := (HilbertChart.AffineRestriction.translationProductRight_isPullback
    (B := B) (t i)).map (Over.forget _)
  obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback H.flip y w hw.symm
  exact ⟨i, z, hz⟩

/-- A joint translation cover detects the independent full-fiber locus exactly. -/
theorem fullFiberLocus_translationCover (U : (prod B W).left.Opens) :
    SchemeOpenEnvelope.fullFiberLocus (prod.fst : prod B W ⟶ B).left U =
      ⋂ i, SchemeOpenEnvelope.fullFiberLocus (prod.fst : prod B (T i) ⟶ B).left
        ((prod.map (𝟙 B) (t i)).left ⁻¹ᵁ U) := by
  rw [SchemeOpenEnvelope.fullFiberLocus_jointCover _ _ _
    (translationEnvelope_jointCover B W T t ht)]
  congr 1
  funext i
  have h := congrArg Over.Hom.left (prod.map_fst (𝟙 B) (t i))
  simpa only [Over.comp_left, Category.comp_id] using
    congrArg (fun p ↦ SchemeOpenEnvelope.fullFiberLocus p
      ((prod.map (𝟙 B) (t i)).left ⁻¹ᵁ U)) h

end FLT.Mazur.SchemeTranslationNorm
