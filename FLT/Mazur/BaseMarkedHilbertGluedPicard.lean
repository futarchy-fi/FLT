/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertGluedBase

/-!
# The original Picard section on the scheme over its translation base

The same-base pairwise pullbacks make the original chart classes compatible.
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
  (V : Over (Spec (.of R))) {ι : Type} (a : ι → BaseMarkedHilbertIndex f V)

/-- Equality in the glued scheme produces a map to the actual original pair overlap. -/
theorem baseMarkedGlued_pair_lift (i j : ι) {U : Over (Spec (.of R))}
    (p : U ⟶ variableHilbertTest f (a i).1 V) (q : U ⟶ variableHilbertTest f (a j).1 V)
    (h : p ≫ baseMarkedGluedArrow f hL V a i =
      q ≫ baseMarkedGluedArrow f hL V a j) :
    ∃ b : U ⟶ baseMarkedChartOverlap f hL V (a i) (a j),
      b ≫ baseMarkedChartOverlapLeft f hL V (a i) (a j) = p ∧
        b ≫ baseMarkedChartOverlapRight f hL V (a i) (a j) = q := by
  let pb := baseMarkedGluedChart_isPullback f hL V a i j
  let b := pb.lift p.left q.left (congrArg Over.Hom.left h)
  have hb : b ≫ (baseMarkedChartOverlapLeft f hL V (a i) (a j)).left = p.left :=
    pb.lift_fst _ _ _
  refine ⟨Over.homMk b ?_, ?_, ?_⟩
  · rw [← Over.w (baseMarkedChartOverlapLeft f hL V (a i) (a j)),
      ← Category.assoc, hb, Over.w]
  · exact Over.OverMorphism.ext hb
  · exact Over.OverMorphism.ext (pb.lift_snd _ _ _)

/-- The original Picard classes of the unchanged charts form a compatible family. -/
theorem baseMarkedGlued_classes_compatible :
    Presieve.Arrows.Compatible ((relativeFppfSheaf f).obj ⋙ forget CommGrpCat)
      (baseMarkedGluedArrow f hL V a) (fun i ↦ baseMarkedChartSection f hL V (a i)) := by
  intro i j U p q h
  obtain ⟨b, hp, hq⟩ := baseMarkedGlued_pair_lift f hL V a i j p q h
  change (relativeFppfSheaf f).obj.map p.op _ = (relativeFppfSheaf f).obj.map q.op _
  rw [baseMarkedChartSection_map, baseMarkedChartSection_map, ← hp, ← hq]
  exact baseMarkedOverlap_restrict_class f hL V (a i) (a j) b

/-- The chart arrows satisfy descent for the original Picard sheaf. -/
theorem baseMarkedGlued_isSheafFor :
    Presieve.IsSheafFor ((relativeFppfSheaf f).obj ⋙ forget CommGrpCat)
      (Presieve.ofArrows (fun i ↦ variableHilbertTest f (a i).1 V)
        (baseMarkedGluedArrow f hL V a)) := by
  have hs := (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget CommGrpCat)).mp
    (relativeFppfSheaf f).property
  rw [isSheaf_iff_isSheaf_of_type] at hs
  apply hs.isSheafFor
  rw [GrothendieckTopology.mem_over_iff, ← Sieve.ofArrows, Sieve.overEquiv_ofArrows]
  exact Precoverage.generate_mem_toGrothendieck
    (Scheme.zariskiPrecoverage_le_fppfPrecoverage _ (baseMarkedGluedCover f hL V a).mem₀)

/-- There is one and only one original Picard section with the prescribed chart classes. -/
theorem baseMarkedGluedPicard_existsUnique :
    ∃! s : (relativeFppfSheaf f).obj.obj (op (baseMarkedGluedTest f hL V a)),
      ∀ i, (relativeFppfSheaf f).obj.map (baseMarkedGluedArrow f hL V a i).op s =
        baseMarkedChartSection f hL V (a i) := by
  have h := baseMarkedGlued_isSheafFor f hL V a
  rw [Presieve.isSheafFor_arrows_iff] at h
  exact h _ (baseMarkedGlued_classes_compatible f hL V a)

/-- The constructed original Picard-sheaf section on the glued parameter scheme. -/
def baseMarkedGluedPicard :
    (relativeFppfSheaf f).obj.obj (op (baseMarkedGluedTest f hL V a)) :=
  (baseMarkedGluedPicard_existsUnique f hL V a).choose

/-- The glued section recovers each original translated parameter class. -/
theorem baseMarkedGluedPicard_chart (i : ι) :
    (relativeFppfSheaf f).obj.map (baseMarkedGluedArrow f hL V a i).op
        (baseMarkedGluedPicard f hL V a) = baseMarkedChartSection f hL V (a i) :=
  (baseMarkedGluedPicard_existsUnique f hL V a).choose_spec.1 i

end FLT.Mazur.HilbertChart
