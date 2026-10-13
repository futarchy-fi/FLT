/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AcyclicHilbertFixedBaseProjection

/-!
# The Hilbert parameter projection recovers every original morphism

The full divisor equivalences make parameter transport injective. Combined
with the constructed projection, this proves its other inverse identity on
arbitrary tests, retaining the entire Hilbert parameter.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open FCurve CartierAbel SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R R' : Type} [CommRing R] [CommRing R']
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R']
  {X : Scheme} (f : X ⟶ Spec (.of R)) (a : Spec (.of R') ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L) (d : ℕ)
local notation "q" => Limits.pullback.snd f a
local instance : SmoothOfRelativeDimension 1 q :=
  MorphismProperty.pullback_snd _ _ inferInstance

/-- Full Hilbert parameter transport is injective on arbitrary scheme-valued tests. -/
theorem acyclicHilbertFixedBaseParameter_injective (T : Over (Spec (.of R'))) :
    Function.Injective (acyclicHilbertFixedBaseParameter f a hL d T) :=
  (acyclicHilbertDegreeEquiv q d (fixedBaseAmple f a hL) T).symm.injective.comp
    ((acyclicDegreeFixedBaseEquiv f a d T).injective.comp
      (acyclicHilbertDegreeEquiv f d hL ((Over.map a).obj T)).injective)

/-- Projecting a transported parameter recovers the ORIGINAL Hilbert scheme morphism. -/
theorem acyclicHilbertFixedBaseParameter_projection (T : Over (Spec (.of R')))
    (k : (Over.map a).obj T ⟶ acyclicHilbertTest f d) :
    (Over.map a).map (acyclicHilbertFixedBaseParameter f a hL d T k) ≫
      acyclicHilbertFixedBaseProjection f a hL d = k := by
  apply acyclicHilbertFixedBaseParameter_injective f a hL d T
  exact acyclicHilbertFixedBaseProjection_parameter f a hL d T _

end FLT.Mazur.HilbertChart
