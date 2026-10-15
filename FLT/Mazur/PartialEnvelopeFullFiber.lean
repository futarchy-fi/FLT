/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.JointEnvelopeFullFiber

/-!
# Partial covers of the complement of an envelope open

Only points outside the requested open need chart preimages. A compact
complement and open chart images then give a finite family of such charts.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeOpenEnvelope
universe u v
variable {X Y : Scheme.{u}} (π : Y ⟶ X)
  {I : Type v} (E : I → Scheme.{u}) (g : ∀ i, E i ⟶ Y) (U : Y.Opens)

/-- A cover of the bad points suffices to test the entire ambient fiber. -/
theorem fullFiberLocus_partialCover
    (hg : ∀ y : Y, y ∉ U → ∃ i, ∃ z : E i, g i z = y) :
    fullFiberLocus π U = ⋂ i, fullFiberLocus (g i ≫ π) (g i ⁻¹ᵁ U) := by
  ext x
  simp only [Set.mem_iInter, mem_fullFiberLocus]
  constructor
  · intro h i z hz
    exact h (g i z) hz
  · intro h y hy
    by_contra hn
    obtain ⟨i, z, rfl⟩ := hg y hn
    exact hn (h i z hy)

omit π in
/-- Compactness selects finitely many open chart images covering the bad locus. -/
theorem exists_finite_partialCover
    (hU : IsCompact (U : Set Y)ᶜ) (ho : ∀ i, IsOpen (Set.range (g i)))
    (hg : ∀ y : Y, y ∉ U → ∃ i, ∃ z : E i, g i z = y) :
    ∃ J : Finset I, ∀ y : Y, y ∉ U → ∃ i ∈ J, ∃ z : E i, g i z = y := by
  obtain ⟨J, hJ⟩ := hU.elim_finite_subcover (fun i ↦ Set.range (g i)) ho (by
    intro y hy
    obtain ⟨i, z, hz⟩ := hg y hy
    exact Set.mem_iUnion.mpr ⟨i, z, hz⟩)
  refine ⟨J, fun y hy ↦ ?_⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hJ hy)
  obtain ⟨hiJ, z, hz⟩ := Set.mem_iUnion.mp hi
  exact ⟨i, hiJ, z, hz⟩

end FLT.Mazur.SchemeOpenEnvelope

namespace FLT.Mazur.SchemeTranslationNorm
universe v
variable {R : Type} [CommRing R] (B W : Over (Spec (.of R)))
  {I : Type v} (T : I → Over (Spec (.of R))) (t : ∀ i, T i ⟶ W)
  (U : (prod B W).left.Opens)

/-- A preimage of each bad point's translation coordinate lifts that exact envelope point. -/
theorem translationEnvelope_partialCover
    (ht : ∀ y : (prod B W).left, y ∉ U →
      ∃ i, ∃ z : (T i).left, (t i).left z = (prod.snd : prod B W ⟶ W).left y)
    (y : (prod B W).left) (hy : y ∉ U) :
    ∃ i, ∃ z : (prod B (T i)).left, (prod.map (𝟙 B) (t i)).left z = y := by
  obtain ⟨i, z, hz⟩ := ht y hy
  have H := (HilbertChart.AffineRestriction.translationProductRight_isPullback
    (B := B) (t i)).map (Over.forget _)
  obtain ⟨e, he, _⟩ := Scheme.exists_preimage_of_isPullback H.flip y z hz.symm
  exact ⟨i, e, he⟩

/-- Partial translation charts detect fullness when they cover every bad coordinate. -/
theorem fullFiberLocus_partialTranslationCover
    (ht : ∀ y : (prod B W).left, y ∉ U →
      ∃ i, ∃ z : (T i).left, (t i).left z = (prod.snd : prod B W ⟶ W).left y) :
    SchemeOpenEnvelope.fullFiberLocus (prod.fst : prod B W ⟶ B).left U =
      ⋂ i, SchemeOpenEnvelope.fullFiberLocus (prod.fst : prod B (T i) ⟶ B).left
        ((prod.map (𝟙 B) (t i)).left ⁻¹ᵁ U) := by
  rw [SchemeOpenEnvelope.fullFiberLocus_partialCover _ _ _ _
    (translationEnvelope_partialCover B W T t U ht)]
  congr 1
  funext i
  have h := congrArg Over.Hom.left (prod.map_fst (𝟙 B) (t i))
  simpa only [Over.comp_left, Category.comp_id] using
    congrArg (fun p ↦ SchemeOpenEnvelope.fullFiberLocus p
      ((prod.map (𝟙 B) (t i)).left ⁻¹ᵁ U)) h

end FLT.Mazur.SchemeTranslationNorm
