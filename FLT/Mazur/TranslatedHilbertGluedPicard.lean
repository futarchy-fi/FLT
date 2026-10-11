/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranslatedHilbertGluedBase

/-!
# The original Picard section on the glued translated charts

The full pairwise pullbacks make the original chart classes compatible.
Fppf sheaf descent along the constructed open cover glues them uniquely.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  {ι : Type} (a : ι → TranslatedHilbertIndex f)

/-- Equality in the glued scheme produces a map to the actual original pair overlap. -/
theorem translatedHilbertGlued_pair_lift (i j : ι) {U : Over (Spec (.of R))}
    (p : U ⟶ acyclicHilbertTest f (a i).1) (q : U ⟶ acyclicHilbertTest f (a j).1)
    (h : p ≫ translatedHilbertGluedArrow f hL a i =
      q ≫ translatedHilbertGluedArrow f hL a j) :
    ∃ b : U ⟶ translatedHilbertChartOverlap f hL (a i) (a j),
      b ≫ translatedHilbertChartOverlapLeft f hL (a i) (a j) = p ∧
        b ≫ translatedHilbertChartOverlapRight f hL (a i) (a j) = q := by
  let pb := translatedHilbertGluedChart_isPullback f hL a i j
  let b := pb.lift p.left q.left (congrArg Over.Hom.left h)
  have hb : b ≫ (translatedHilbertChartOverlapLeft f hL (a i) (a j)).left = p.left :=
    pb.lift_fst _ _ _
  refine ⟨Over.homMk b ?_, ?_, ?_⟩
  · rw [← Over.w (translatedHilbertChartOverlapLeft f hL (a i) (a j)),
      ← Category.assoc, hb, Over.w]
  · exact Over.OverMorphism.ext hb
  · exact Over.OverMorphism.ext (pb.lift_snd _ _ _)

/-- The original Picard classes of the unchanged charts form a compatible family. -/
theorem translatedHilbertGlued_classes_compatible :
    Presieve.Arrows.Compatible ((relativeFppfSheaf f).obj ⋙ forget CommGrpCat)
      (translatedHilbertGluedArrow f hL a) (fun i ↦ translatedHilbertChartSection f hL (a i)) := by
  intro i j U p q h
  obtain ⟨b, hp, hq⟩ := translatedHilbertGlued_pair_lift f hL a i j p q h
  change (relativeFppfSheaf f).obj.map p.op _ = (relativeFppfSheaf f).obj.map q.op _
  rw [translatedHilbertChartSection_map, translatedHilbertChartSection_map, ← hp, ← hq]
  exact translatedHilbertOverlap_restrict_class f hL (a i) (a j) b

/-- The chart arrows satisfy descent for the original Picard sheaf. -/
theorem translatedHilbertGlued_isSheafFor :
    Presieve.IsSheafFor ((relativeFppfSheaf f).obj ⋙ forget CommGrpCat)
      (Presieve.ofArrows (fun i ↦ acyclicHilbertTest f (a i).1)
        (translatedHilbertGluedArrow f hL a)) := by
  have hs := (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget CommGrpCat)).mp
    (relativeFppfSheaf f).property
  rw [isSheaf_iff_isSheaf_of_type] at hs
  apply hs.isSheafFor
  rw [GrothendieckTopology.mem_over_iff, ← Sieve.ofArrows, Sieve.overEquiv_ofArrows]
  exact Precoverage.generate_mem_toGrothendieck
    (Scheme.zariskiPrecoverage_le_fppfPrecoverage _ (translatedHilbertGluedCover f hL a).mem₀)

/-- There is one and only one original Picard section with the prescribed chart classes. -/
theorem translatedHilbertGluedPicard_existsUnique :
    ∃! s : (relativeFppfSheaf f).obj.obj (op (translatedHilbertGluedTest f hL a)),
      ∀ i, (relativeFppfSheaf f).obj.map (translatedHilbertGluedArrow f hL a i).op s =
        translatedHilbertChartSection f hL (a i) := by
  have h := translatedHilbertGlued_isSheafFor f hL a
  rw [Presieve.isSheafFor_arrows_iff] at h
  exact h _ (translatedHilbertGlued_classes_compatible f hL a)

/-- The constructed original Picard-sheaf section on the glued parameter scheme. -/
def translatedHilbertGluedPicard :
    (relativeFppfSheaf f).obj.obj (op (translatedHilbertGluedTest f hL a)) :=
  (translatedHilbertGluedPicard_existsUnique f hL a).choose

/-- The glued section recovers each original translated parameter class. -/
theorem translatedHilbertGluedPicard_chart (i : ι) :
    (relativeFppfSheaf f).obj.map (translatedHilbertGluedArrow f hL a i).op
        (translatedHilbertGluedPicard f hL a) = translatedHilbertChartSection f hL (a i) :=
  (translatedHilbertGluedPicard_existsUnique f hL a).choose_spec.1 i

end FLT.Mazur.HilbertChart
