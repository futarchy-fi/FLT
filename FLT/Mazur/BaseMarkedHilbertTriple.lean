/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertIdentities

/-!
# Actual triple intersections of base-marked Hilbert charts

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
  (V : Over (Spec (.of R))) (i j k : BaseMarkedHilbertIndex f V)

/-- The scheme-theoretic triple intersection, still over the original base. -/
abbrev baseMarkedTripleTest : Over (Spec (.of R)) :=
  pullback (baseMarkedChartOverlapLeft f hL V i j)
    (baseMarkedChartOverlapLeft f hL V i k)

/-- On a triple intersection, the two remaining parameter classes coincide. -/
theorem baseMarkedTriple_class :
    variableHilbertPoint f j.1 hL V j.2 (baseMarkedTripleTest f hL V i j k)
        (pullback.fst _ _ ≫ baseMarkedChartOverlapRight f hL V i j) =
      variableHilbertPoint f k.1 hL V k.2 _
        (pullback.snd _ _ ≫ baseMarkedChartOverlapRight f hL V i k) := by
  exact (baseMarkedOverlap_restrict_class f hL V i j (pullback.fst _ _)).symm.trans
    ((congrArg (variableHilbertPoint f i.1 hL V i.2 _) pullback.condition).trans
      (baseMarkedOverlap_restrict_class f hL V i k (pullback.snd _ _)))

/-- The two remaining charts also retain the same map to the translation base. -/
theorem baseMarkedTriple_base :
    (pullback.snd (baseMarkedChartOverlapLeft f hL V i j)
        (baseMarkedChartOverlapLeft f hL V i k) ≫ baseMarkedChartOverlapRight f hL V i k) ≫
        variableHilbertBase f k.1 V =
      (pullback.fst _ _ ≫ baseMarkedChartOverlapRight f hL V i j) ≫
        variableHilbertBase f j.1 V := by
  simp only [Category.assoc, baseMarkedChartOverlap_base]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m ↦ m ≫ variableHilbertBase f i.1 V) pullback.condition.symm).trans
      (Category.assoc _ _ _))

/-- The constructed map from the full triple intersection to the third pair overlap. -/
def baseMarkedTripleRoute :
    baseMarkedTripleTest f hL V i j k ⟶ baseMarkedChartOverlap f hL V j k :=
  (baseMarkedChartOverlap_lift f hL V j k
    (pullback.fst _ _ ≫ baseMarkedChartOverlapRight f hL V i j)
    (pullback.snd _ _ ≫ baseMarkedChartOverlapRight f hL V i k)
    (baseMarkedTriple_base f hL V i j k)
    (baseMarkedTriple_class f hL V i j k)).choose

@[reassoc]
lemma baseMarkedTripleRoute_left :
    baseMarkedTripleRoute f hL V i j k ≫ baseMarkedChartOverlapLeft f hL V j k =
      pullback.fst _ _ ≫ baseMarkedChartOverlapRight f hL V i j :=
  (baseMarkedChartOverlap_lift f hL V j k _ _
    (baseMarkedTriple_base f hL V i j k)
    (baseMarkedTriple_class f hL V i j k)).choose_spec.1.1

@[reassoc]
lemma baseMarkedTripleRoute_right :
    baseMarkedTripleRoute f hL V i j k ≫ baseMarkedChartOverlapRight f hL V j k =
      pullback.snd _ _ ≫ baseMarkedChartOverlapRight f hL V i k :=
  (baseMarkedChartOverlap_lift f hL V j k _ _
    (baseMarkedTriple_base f hL V i j k)
    (baseMarkedTriple_class f hL V i j k)).choose_spec.1.2

/-- Rotate the three actual charts, retaining the full scheme-theoretic intersections. -/
def baseMarkedTripleRotate :
    baseMarkedTripleTest f hL V i j k ⟶ baseMarkedTripleTest f hL V j k i :=
  pullback.lift (baseMarkedTripleRoute f hL V i j k)
    (pullback.fst _ _ ≫ baseMarkedChartOverlapSwap f hL V i j) (by
      rw [Category.assoc, baseMarkedChartOverlapSwap_left,
        baseMarkedTripleRoute_left])

@[reassoc]
lemma baseMarkedTripleRotate_fst :
    baseMarkedTripleRotate f hL V i j k ≫ pullback.fst _ _ =
      baseMarkedTripleRoute f hL V i j k :=
  pullback.lift_fst _ _ _

@[reassoc]
lemma baseMarkedTripleRotate_snd :
    baseMarkedTripleRotate f hL V i j k ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ baseMarkedChartOverlapSwap f hL V i j :=
  pullback.lift_snd _ _ _

end FLT.Mazur.HilbertChart
