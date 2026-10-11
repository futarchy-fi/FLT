/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmallHilbertTranslationAtlas
public import FLT.Mazur.VariableTranslatedHilbertRepresentation

/-!
# Represented pullbacks of the fixed small Hilbert chart family

Every chart has a represented intersection with every original Picard
section. The intersection morphisms are locally of finite presentation
because the chosen translation bases are. Smoothness is not inferred.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel FCurve SchemePicard Approximation
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {B : X.Modules} (hB : AmpleLineBundle B)
  (i : SmallHilbertTranslationIndex f)

/-- The natural original Picard map of a chosen small chart. -/
def smallHilbertChartMap : uliftYoneda.{1}.obj (smallHilbertTranslationTest f i) ⟶
    (relativeFppfSheaf f).obj ⋙ forget CommGrpCat :=
  variableHilbertPicardMap f i.2 hB (relativeLineParameterTest f i.1)
    (relativeLineParameterClass f i.1)

variable (T : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op T))

/-- The original test intersection with a chosen small chart is represented. -/
theorem smallHilbertChartMap_isPullback :
    IsPullback (uliftYoneda.{1}.map (variableHilbertOverlapToChart f i.2 hB
        (relativeLineParameterTest f i.1) (relativeLineParameterClass f i.1) T s))
      (uliftYoneda.{1}.map (variableHilbertOverlapToTest f i.2
        (relativeLineParameterTest f i.1) (relativeLineParameterClass f i.1) T s))
      (smallHilbertChartMap f hB i) (uliftYonedaEquiv.symm s) :=
  variableHilbertPicardMap_isPullback f i.2 hB _ _ T s

/-- Actual small-chart pullbacks are locally of finite presentation over the input test. -/
instance smallHilbertOverlapToTest_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (variableHilbertOverlapToTest f i.2
      (relativeLineParameterTest f i.1) (relativeLineParameterClass f i.1) T s).left := by
  let V := relativeLineParameterTest f i.1
  let _ : LocallyOfFinitePresentation V.hom :=
    affinePresentationTest_locallyOfFinitePresentation _ i.1.1
  let _ : LocallyOfFinitePresentation (prod.fst : prod T V ⟶ T).left := by
    rw [← Over.prodLeftIsoPullback_hom_fst T V]
    infer_instance
  change LocallyOfFinitePresentation ((variableHilbertOverlapArrow f i.2 V
    (relativeLineParameterClass f i.1) T s).left ≫ (prod.fst : prod T V ⟶ T).left)
  infer_instance

include hB in
/-- The represented small-chart intersections generate a covering sieve of every input test. -/
theorem smallHilbertOverlap_covering :
    Sieve.ofArrows
      (fun i : SmallHilbertTranslationIndex f ↦ variableHilbertOverlap f i.2
        (relativeLineParameterTest f i.1) (relativeLineParameterClass f i.1) T s)
      (fun i ↦ variableHilbertOverlapToTest f i.2
        (relativeLineParameterTest f i.1) (relativeLineParameterClass f i.1) T s) ∈
      (Scheme.fppfTopology.over (Spec (.of R))) T := by
  obtain ⟨C, _, hC⟩ := exists_small_hilbert_translation_cover f hB T s
  have hcov : Sieve.ofArrows (relativeCoverMember T C) (relativeCoverArrow T C) ∈
      (Scheme.fppfTopology.over (Spec (.of R))) T := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact Precoverage.generate_mem_toGrothendieck C.mem₀
  apply (Scheme.fppfTopology.over (Spec (.of R))).superset_covering ?_ hcov
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro _ _ ⟨j⟩
  obtain ⟨i, k, hk⟩ := hC j
  obtain ⟨l, hl, _⟩ := variableHilbertOverlap_lift f i.2 hB
    (relativeLineParameterTest f i.1) (relativeLineParameterClass f i.1) T s
    (relativeCoverArrow T C j) k hk
  exact (Sieve.mem_ofArrows_iff _ _ _).mpr ⟨i, l, hl.1.symm⟩

end FLT.Mazur.HilbertChart
