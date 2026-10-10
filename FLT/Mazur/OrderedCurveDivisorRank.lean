/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedCurveDivisorLocalFree
public import FLT.Mazur.SectionSumRank

/-!
# Exact degree of the universal ordered divisor

The universal graph-product family and every specialized tuple are finite locally
free of rank `n`. Residue-field lengths count every factor, so repeated points and
empty tuples require no exceptions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.OrderedCurvePower

open FCurve

variable {X S : Scheme.{0}} (f : X ⟶ S) (n : ℕ)
  [SmoothOfRelativeDimension 1 f] [IsProper f]

/-- The universal ordered graph divisor is finite locally free of degree `n`. -/
theorem divisorToBase_finiteLocallyFreeDegree :
    FiniteLocallyFreeDegree (divisorToBase f n) n := by
  let _ : SmoothOfRelativeDimension 1 (projection f n) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) f (base f n)
      inferInstance
  simpa only [divisorToBase, divisorScheme, divisorIdeal,
    Finset.card_univ, Fintype.card_fin] using
    finiteLocallyFreeDegree_section_prod (projection f n) Finset.univ (graph f n)
      (graph_projection f n)

/-- Its actual geometric rank is `n` at every parameter, including every diagonal. -/
theorem divisorToBase_finrank (y : space f n) : (divisorToBase f n).finrank y = n :=
  (divisorToBase_finiteLocallyFreeDegree f n).2.2.2 y

variable {T : Scheme.{0}} (g : T ⟶ S) (x : Fin n → (T ⟶ X))
  (hx : ∀ i, x i ≫ f = g)

/-- Every supplied tuple gives a finite locally free divisor of the prescribed degree. -/
theorem tupleDivisor_finiteLocallyFreeDegree :
    FiniteLocallyFreeDegree
      ((tupleDivisorIdeal f n g x hx).subschemeι ≫ pullback.snd f g) n := by
  let _ : SmoothOfRelativeDimension 1 (pullback.snd f g) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) f g inferInstance
  simpa only [tupleDivisorIdeal, Finset.card_univ, Fintype.card_fin] using
    finiteLocallyFreeDegree_section_prod (pullback.snd f g) Finset.univ
      (fun i ↦ CurveGraphPullback.graph f g (x i) (hx i))
      (fun i ↦ CurveGraphPullback.graph_snd f g (x i) (hx i))

/-- A nonempty tuple's divisor surjects onto its whole test scheme. -/
theorem tupleDivisor_surjective (hn : 0 < n) :
    Surjective ((tupleDivisorIdeal f n g x hx).subschemeι ≫ pullback.snd f g) :=
  (tupleDivisor_finiteLocallyFreeDegree f n g x hx).surjective hn

end FLT.Mazur.OrderedCurvePower
