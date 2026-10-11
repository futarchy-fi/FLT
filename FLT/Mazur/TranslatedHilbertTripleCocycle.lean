/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranslatedHilbertTripleOverlap
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# The translated Hilbert triple cocycle

Three rotations return the original full intersection. These constructed maps,
including the diagonal identity, give categorical gluing data over the base.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] translatedHilbertTripleRotate translatedHilbertTripleRoute
  translatedHilbertChartOverlapLeft translatedHilbertChartOverlapRight
  translatedHilbertChartOverlapSwap translatedHilbertChartOverlap acyclicHilbertTest
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (i j k : TranslatedHilbertIndex f)

/-- A sealed first parameter coordinate on the actual triple intersection. -/
@[irreducible]
def translatedHilbertTripleFirst :
    translatedHilbertTripleTest f hL i j k ⟶ acyclicHilbertTest f i.1 :=
  pullback.fst _ _ ≫ translatedHilbertChartOverlapLeft f hL i j

/-- A sealed second parameter coordinate on the actual triple intersection. -/
@[irreducible]
def translatedHilbertTripleSecond :
    translatedHilbertTripleTest f hL i j k ⟶ acyclicHilbertTest f j.1 :=
  pullback.fst _ _ ≫ translatedHilbertChartOverlapRight f hL i j

/-- A sealed third parameter coordinate on the actual triple intersection. -/
@[irreducible]
def translatedHilbertTripleThird :
    translatedHilbertTripleTest f hL i j k ⟶ acyclicHilbertTest f k.1 :=
  pullback.snd _ _ ≫ translatedHilbertChartOverlapRight f hL i k

instance translatedHilbertTripleFirst_mono : Mono (translatedHilbertTripleFirst f hL i j k) := by
  unfold translatedHilbertTripleFirst
  infer_instance

@[reassoc]
lemma translatedHilbertTripleRotate_first :
    translatedHilbertTripleRotate f hL i j k ≫ translatedHilbertTripleFirst f hL j k i =
      translatedHilbertTripleSecond f hL i j k := by
  rw [translatedHilbertTripleFirst, translatedHilbertTripleSecond, ← Category.assoc,
    translatedHilbertTripleRotate_fst, translatedHilbertTripleRoute_left]

@[reassoc]
lemma translatedHilbertTripleRotate_second :
    translatedHilbertTripleRotate f hL i j k ≫ translatedHilbertTripleSecond f hL j k i =
      translatedHilbertTripleThird f hL i j k := by
  rw [translatedHilbertTripleSecond, translatedHilbertTripleThird, ← Category.assoc,
    translatedHilbertTripleRotate_fst, translatedHilbertTripleRoute_right]

@[reassoc]
lemma translatedHilbertTripleRotate_third :
    translatedHilbertTripleRotate f hL i j k ≫ translatedHilbertTripleThird f hL j k i =
      translatedHilbertTripleFirst f hL i j k := by
  rw [translatedHilbertTripleThird, translatedHilbertTripleFirst, ← Category.assoc,
    translatedHilbertTripleRotate_snd, Category.assoc, translatedHilbertChartOverlapSwap_right]

/-- The rotation cocycle holds on the actual scheme-theoretic triple intersection. -/
theorem translatedHilbertTripleRotate_cocycle :
    translatedHilbertTripleRotate f hL i j k ≫ translatedHilbertTripleRotate f hL j k i ≫
      translatedHilbertTripleRotate f hL k i j = 𝟙 _ := by
  apply (cancel_mono (translatedHilbertTripleFirst f hL i j k)).mp
  rw [Category.assoc, Category.assoc, translatedHilbertTripleRotate_first,
    translatedHilbertTripleRotate_second, translatedHilbertTripleRotate_third, Category.id_comp]


end FLT.Mazur.HilbertChart
