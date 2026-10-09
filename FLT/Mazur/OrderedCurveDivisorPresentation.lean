/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierImmersionFinitePresentation
public import FLT.Mazur.OrderedCurveDivisorFinite
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# Finite presentation of the ordered divisor family

The actual graph-product immersion is finitely presented because it is Cartier.
Together with finite flatness this gives locally constant rank over arbitrary
bases, including non-Noetherian bases and loci where the ordered points collide.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.OrderedCurvePower

open FCurve

variable {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
  [SmoothOfRelativeDimension 1 f] [IsSeparated f]

/-- The universal graph product is locally of finite presentation over its parameters. -/
theorem divisorToBase_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (divisorToBase f n) := by
  let _ := SmoothOfRelativeDimension.smooth 1 f
  exact (divisor_relativeEffectiveCartier f n).1.locallyOfFinitePresentation_comp (projection f n)

omit [IsSeparated f] in
/-- The rank of the finite flat universal divisor is locally constant. -/
theorem divisorToBase_isLocallyConstant_finrank [IsProper f] :
    IsLocallyConstant (divisorToBase f n).finrank := by
  let _ := divisorToBase_isFinite f n
  let _ := divisorToBase_flat f n
  let _ := divisorToBase_locallyOfFinitePresentation f n
  exact (divisorToBase f n).isLocallyConstant_finrank

variable {T : Scheme.{u}} (g : T ⟶ S) (x : Fin n → (T ⟶ X))
  (hx : ∀ i, x i ≫ f = g)

/-- Every tuple's Cartier graph sum is locally of finite presentation over the test scheme. -/
theorem tupleDivisor_locallyOfFinitePresentation :
    LocallyOfFinitePresentation
      ((tupleDivisorIdeal f n g x hx).subschemeι ≫ pullback.snd f g) := by
  let _ := SmoothOfRelativeDimension.smooth 1 f
  exact (tupleDivisor_relativeEffectiveCartier f n g x hx).1.locallyOfFinitePresentation_comp _

omit [IsSeparated f] in
/-- The actual rank of a specialized graph divisor is locally constant. -/
theorem tupleDivisor_isLocallyConstant_finrank [IsProper f] :
    IsLocallyConstant
      ((tupleDivisorIdeal f n g x hx).subschemeι ≫ pullback.snd f g).finrank := by
  let _ := tupleDivisor_isFinite f n g x hx
  let _ := (tupleDivisor_relativeEffectiveCartier f n g x hx).2
  let _ := tupleDivisor_locallyOfFinitePresentation f n g x hx
  exact Scheme.Hom.isLocallyConstant_finrank _

end FLT.Mazur.OrderedCurvePower
