/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedCurveDivisor
public import FLT.Mazur.CurveGraphPullback

/-!
# Specializing the universal ordered divisor

Pullback along the unique classifying map is the actual product of the graphs of
the specified points. This statement allows arbitrary parameter schemes and base
maps, without flatness or pairwise distinctness conditions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.OrderedCurvePower

open FCurve

variable {X S T : Scheme.{u}} (f : X ⟶ S) (n : ℕ) (g : T ⟶ S)
  (x : Fin n → (T ⟶ X)) (hx : ∀ i, x i ≫ f = g)

/-- The map from the curve of the specified tuple to the universal curve. -/
def classifyingCurveMap : pullback f g ⟶ curve f n :=
  CurveGraphPullback.curveMap f (base f n) g (classify f n g x hx)
    (classify_base f n g x hx)

/-- The family map lies in an actual cartesian square. -/
theorem classifyingCurveMap_isPullback :
    IsPullback (classifyingCurveMap f n g x hx) (pullback.snd f g)
      (projection f n) (classify f n g x hx) :=
  CurveGraphPullback.curveMap_isPullback _ _ _ _ _

/-- A single universal graph specializes to the corresponding supplied point. -/
theorem graph_ker_classifying_comap [IsSeparated f] (i : Fin n) :
    (graph f n i).ker.comap (classifyingCurveMap f n g x hx) =
      (CurveGraphPullback.graph f g (x i) (hx i)).ker := by
  change (CurveGraphPullback.graph f (base f n) (point f n i) (point_base f n i)).ker.comap
    (CurveGraphPullback.curveMap f (base f n) g (classify f n g x hx)
      (classify_base f n g x hx)) = _
  rw [CurveGraphPullback.graph_ker_comap]
  simp only [classify_point]

/-- The ideal defined by any tuple of points, with repetitions retained. -/
def tupleDivisorIdeal : (pullback f g).IdealSheafData :=
  ∏ i : Fin n, (CurveGraphPullback.graph f g (x i) (hx i)).ker

/-- Pullback of the universal divisor recovers the tuple's actual graph sum. -/
theorem divisorIdeal_classifying_comap [IsSeparated f] :
    (divisorIdeal f n).comap (classifyingCurveMap f n g x hx) =
      tupleDivisorIdeal f n g x hx := by
  simp only [divisorIdeal, tupleDivisorIdeal, idealSheaf_comap_prod,
    graph_ker_classifying_comap]

/-- Every specialized graph sum is relative Cartier on a smooth separated curve. -/
theorem tupleDivisor_relativeEffectiveCartier
    [SmoothOfRelativeDimension 1 f] [IsSeparated f] :
    RelativeEffectiveCartier (pullback.snd f g) (tupleDivisorIdeal f n g x hx) := by
  let _ : SmoothOfRelativeDimension 1 (pullback.snd f g) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) f g inferInstance
  exact relativeEffectiveCartier_section_prod (pullback.snd f g) Finset.univ
    (fun i ↦ CurveGraphPullback.graph f g (x i) (hx i))
    (fun i _ ↦ CurveGraphPullback.graph_snd f g (x i) (hx i))

end FLT.Mazur.OrderedCurvePower
