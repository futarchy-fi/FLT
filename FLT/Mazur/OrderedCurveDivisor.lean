/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedCurvePower
public import FLT.Mazur.RelativeSums
public import FLT.Mazur.DivisorCanonicalSection
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The universal divisor on the ordered point space

The product of the actual graph ideals is a relative effective Cartier divisor,
including along diagonals where points coincide. Its positive divisor line bundle
and canonical section are constructed from that ideal.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.OrderedCurvePower

open FCurve

variable {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)

/-- The relative curve over the ordered parameter scheme. -/
abbrev curve : Scheme.{u} := pullback f (base f n)

/-- Its structural projection to the parameter scheme. -/
abbrev projection : curve f n ⟶ space f n := pullback.snd f (base f n)

/-- The graph of the `i`-th universal point, as an actual section. -/
def graph (i : Fin n) : space f n ⟶ curve f n :=
  pullback.lift (point f n i) (𝟙 _) (by simp)

@[reassoc (attr := simp)]
lemma graph_fst (i : Fin n) : graph f n i ≫ pullback.fst f (base f n) = point f n i :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma graph_projection (i : Fin n) : graph f n i ≫ projection f n = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The sum of universal graphs, retaining repeated points with multiplicity. -/
def divisorIdeal : (curve f n).IdealSheafData := ∏ i : Fin n, (graph f n i).ker

/-- The empty tuple gives the empty divisor. -/
lemma divisorIdeal_zero : divisorIdeal f 0 = 1 := by simp [divisorIdeal]

variable [SmoothOfRelativeDimension 1 f] [IsSeparated f]

/-- The graph product is relative Cartier without any distinctness assumption. -/
theorem divisor_relativeEffectiveCartier :
    RelativeEffectiveCartier (projection f n) (divisorIdeal f n) := by
  let _ : SmoothOfRelativeDimension 1 (projection f n) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) f (base f n)
      inferInstance
  exact relativeEffectiveCartier_section_prod (projection f n) Finset.univ (graph f n)
    (fun i _ ↦ graph_projection f n i)

/-- The positive universal divisor line, on the actual base-changed curve. -/
def divisorLine : (curve f n).Modules :=
  divisorLineBundle (divisorIdeal f n) (divisor_relativeEffectiveCartier f n).1

/-- The universal divisor line is locally free of rank one. -/
theorem divisorLine_locallyFreeRankOne : LocallyFreeRankOne (divisorLine f n) :=
  (divisor_relativeEffectiveCartier f n).1.divisorLineBundle_locallyFreeRankOne

/-- The canonical section cutting out the graph sum. -/
def divisorSection : structureModule (curve f n) ⟶ divisorLine f n :=
  divisorSectionMap (divisor_relativeEffectiveCartier f n).1

end FLT.Mazur.OrderedCurvePower
