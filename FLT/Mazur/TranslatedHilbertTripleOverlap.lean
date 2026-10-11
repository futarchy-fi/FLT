/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranslatedHilbertOverlapIdentities

/-!
# Actual triple intersections of translated Hilbert charts

Two overlaps over one parameter chart have compatible maps to the other two
charts. Their original Picard classes construct the third overlap map.
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
  (i j k : TranslatedHilbertIndex f)

/-- The scheme-theoretic triple intersection, still over the original base. -/
abbrev translatedHilbertTripleTest : Over (Spec (.of R)) :=
  pullback (translatedHilbertChartOverlapLeft f hL i j)
    (translatedHilbertChartOverlapLeft f hL i k)

/-- On a triple intersection, the two remaining parameter classes coincide. -/
theorem translatedHilbertTriple_class :
    translatedHilbertPicardPoint f j.1 hL j.2 (translatedHilbertTripleTest f hL i j k)
        (pullback.fst _ _ ≫ translatedHilbertChartOverlapRight f hL i j) =
      translatedHilbertPicardPoint f k.1 hL k.2 _
        (pullback.snd _ _ ≫ translatedHilbertChartOverlapRight f hL i k) := by
  exact (translatedHilbertOverlap_restrict_class f hL i j (pullback.fst _ _)).symm.trans
    ((congrArg (translatedHilbertPicardPoint f i.1 hL i.2 _) pullback.condition).trans
      (translatedHilbertOverlap_restrict_class f hL i k (pullback.snd _ _)))

/-- The constructed map from the full triple intersection to the third pair overlap. -/
def translatedHilbertTripleRoute :
    translatedHilbertTripleTest f hL i j k ⟶ translatedHilbertChartOverlap f hL j k :=
  (translatedHilbertChartOverlap_lift f hL j k
    (pullback.fst _ _ ≫ translatedHilbertChartOverlapRight f hL i j)
    (pullback.snd _ _ ≫ translatedHilbertChartOverlapRight f hL i k)
    (translatedHilbertTriple_class f hL i j k)).choose

@[reassoc]
lemma translatedHilbertTripleRoute_left :
    translatedHilbertTripleRoute f hL i j k ≫ translatedHilbertChartOverlapLeft f hL j k =
      pullback.fst _ _ ≫ translatedHilbertChartOverlapRight f hL i j :=
  (translatedHilbertChartOverlap_lift f hL j k _ _
    (translatedHilbertTriple_class f hL i j k)).choose_spec.1.1

@[reassoc]
lemma translatedHilbertTripleRoute_right :
    translatedHilbertTripleRoute f hL i j k ≫ translatedHilbertChartOverlapRight f hL j k =
      pullback.snd _ _ ≫ translatedHilbertChartOverlapRight f hL i k :=
  (translatedHilbertChartOverlap_lift f hL j k _ _
    (translatedHilbertTriple_class f hL i j k)).choose_spec.1.2

/-- Rotate the three actual charts, retaining the full scheme-theoretic intersections. -/
def translatedHilbertTripleRotate :
    translatedHilbertTripleTest f hL i j k ⟶ translatedHilbertTripleTest f hL j k i :=
  pullback.lift (translatedHilbertTripleRoute f hL i j k)
    (pullback.fst _ _ ≫ translatedHilbertChartOverlapSwap f hL i j) (by
      rw [Category.assoc, translatedHilbertChartOverlapSwap_left,
        translatedHilbertTripleRoute_left])

@[reassoc]
lemma translatedHilbertTripleRotate_fst :
    translatedHilbertTripleRotate f hL i j k ≫ pullback.fst _ _ =
      translatedHilbertTripleRoute f hL i j k :=
  pullback.lift_fst _ _ _

@[reassoc]
lemma translatedHilbertTripleRotate_snd :
    translatedHilbertTripleRotate f hL i j k ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ translatedHilbertChartOverlapSwap f hL i j :=
  pullback.lift_snd _ _ _

end FLT.Mazur.HilbertChart
