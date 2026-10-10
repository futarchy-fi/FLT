/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedCurveDivisorPullback
public import FLT.Mazur.SectionSumFinite

/-!
# The finite flat universal ordered divisor

The constructed universal closed subscheme is finite and flat over the ordered
parameter scheme for a smooth proper relative curve. The same holds for every
specified tuple over an arbitrary test scheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.OrderedCurvePower

open FCurve

variable {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)

/-- The actual universal divisor scheme, with the scheme structure of its graph product. -/
abbrev divisorScheme : Scheme.{u} := (divisorIdeal f n).subscheme

/-- The structural morphism of the universal divisor over its parameter scheme. -/
abbrev divisorToBase : divisorScheme f n ⟶ space f n :=
  (divisorIdeal f n).subschemeι ≫ projection f n

/-- Properness alone makes the universal graph sum finite over its parameters. -/
theorem divisorToBase_isFinite [IsProper f] : IsFinite (divisorToBase f n) :=
  isFinite_section_prod (projection f n) Finset.univ (graph f n)
    (fun i _ ↦ graph_projection f n i)

/-- Smoothness supplies flatness of the universal graph divisor, including collisions. -/
theorem divisorToBase_flat [SmoothOfRelativeDimension 1 f] [IsSeparated f] :
    Flat (divisorToBase f n) := (divisor_relativeEffectiveCartier f n).2

/-- The universal ordered divisor is an actual finite flat family. -/
theorem divisorToBase_finite_flat [IsProper f] [SmoothOfRelativeDimension 1 f] :
    IsFinite (divisorToBase f n) ∧ Flat (divisorToBase f n) :=
  ⟨divisorToBase_isFinite f n, divisorToBase_flat f n⟩

variable {T : Scheme.{u}} (g : T ⟶ S) (x : Fin n → (T ⟶ X))
  (hx : ∀ i, x i ≫ f = g)

/-- Every actual tuple produces a finite closed divisor over the test scheme. -/
theorem tupleDivisor_isFinite [IsProper f] :
    IsFinite ((tupleDivisorIdeal f n g x hx).subschemeι ≫ pullback.snd f g) :=
  isFinite_section_prod (pullback.snd f g) Finset.univ
    (fun i ↦ CurveGraphPullback.graph f g (x i) (hx i))
    (fun i _ ↦ CurveGraphPullback.graph_snd f g (x i) (hx i))

/-- The specialized divisor is finite flat over the unchanged test scheme. -/
theorem tupleDivisor_finite_flat [IsProper f] [SmoothOfRelativeDimension 1 f] :
    IsFinite ((tupleDivisorIdeal f n g x hx).subschemeι ≫ pullback.snd f g) ∧
      Flat ((tupleDivisorIdeal f n g x hx).subschemeι ≫ pullback.snd f g) :=
  ⟨tupleDivisor_isFinite f n g x hx, (tupleDivisor_relativeEffectiveCartier f n g x hx).2⟩

end FLT.Mazur.OrderedCurvePower
