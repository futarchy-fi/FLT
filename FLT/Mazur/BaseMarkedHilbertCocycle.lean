/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertTriple
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# The base-marked Hilbert triple cocycle

Three rotations return the original full intersection. These constructed maps,
including the diagonal identity, give categorical gluing data over the base.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] baseMarkedTripleRotate baseMarkedTripleRoute
  baseMarkedChartOverlapLeft baseMarkedChartOverlapRight
  baseMarkedChartOverlapSwap baseMarkedChartOverlap variableHilbertTest
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (V : Over (Spec (.of R))) (i j k : BaseMarkedHilbertIndex f V)

/-- A sealed first parameter coordinate on the actual triple intersection. -/
@[irreducible]
def baseMarkedTripleFirst :
    baseMarkedTripleTest f hL V i j k ⟶ variableHilbertTest f i.1 V :=
  pullback.fst _ _ ≫ baseMarkedChartOverlapLeft f hL V i j

/-- A sealed second parameter coordinate on the actual triple intersection. -/
@[irreducible]
def baseMarkedTripleSecond :
    baseMarkedTripleTest f hL V i j k ⟶ variableHilbertTest f j.1 V :=
  pullback.fst _ _ ≫ baseMarkedChartOverlapRight f hL V i j

/-- A sealed third parameter coordinate on the actual triple intersection. -/
@[irreducible]
def baseMarkedTripleThird :
    baseMarkedTripleTest f hL V i j k ⟶ variableHilbertTest f k.1 V :=
  pullback.snd _ _ ≫ baseMarkedChartOverlapRight f hL V i k

instance baseMarkedTripleFirst_mono : Mono (baseMarkedTripleFirst f hL V i j k) := by
  unfold baseMarkedTripleFirst
  infer_instance

@[reassoc]
lemma baseMarkedTripleRotate_first :
    baseMarkedTripleRotate f hL V i j k ≫ baseMarkedTripleFirst f hL V j k i =
      baseMarkedTripleSecond f hL V i j k := by
  rw [baseMarkedTripleFirst, baseMarkedTripleSecond, ← Category.assoc,
    baseMarkedTripleRotate_fst, baseMarkedTripleRoute_left]

@[reassoc]
lemma baseMarkedTripleRotate_second :
    baseMarkedTripleRotate f hL V i j k ≫ baseMarkedTripleSecond f hL V j k i =
      baseMarkedTripleThird f hL V i j k := by
  rw [baseMarkedTripleSecond, baseMarkedTripleThird, ← Category.assoc,
    baseMarkedTripleRotate_fst, baseMarkedTripleRoute_right]

@[reassoc]
lemma baseMarkedTripleRotate_third :
    baseMarkedTripleRotate f hL V i j k ≫ baseMarkedTripleThird f hL V j k i =
      baseMarkedTripleFirst f hL V i j k := by
  rw [baseMarkedTripleThird, baseMarkedTripleFirst, ← Category.assoc,
    baseMarkedTripleRotate_snd, Category.assoc, baseMarkedChartOverlapSwap_right]

/-- The rotation cocycle holds on the actual scheme-theoretic triple intersection. -/
theorem baseMarkedTripleRotate_cocycle :
    baseMarkedTripleRotate f hL V i j k ≫ baseMarkedTripleRotate f hL V j k i ≫
      baseMarkedTripleRotate f hL V k i j = 𝟙 _ := by
  apply (cancel_mono (baseMarkedTripleFirst f hL V i j k)).mp
  rw [Category.assoc, Category.assoc, baseMarkedTripleRotate_first,
    baseMarkedTripleRotate_second, baseMarkedTripleRotate_third, Category.id_comp]


end FLT.Mazur.HilbertChart
