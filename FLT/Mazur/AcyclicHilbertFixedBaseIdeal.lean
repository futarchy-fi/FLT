/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AcyclicHilbertFixedBaseChange

/-!
# The full universal ideal of the fixed-base Hilbert comparison

The scheme isomorphism acts by the proved transport of full acyclic divisors.
In particular its action on parameters retains the original universal ideal,
including nonreduced structure, under the actual test-curve isomorphism.
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

/-- Transport an original Hilbert parameter to the constructed new-base Hilbert scheme. -/
def acyclicHilbertFixedBaseParameter (T : Over (Spec (.of R')))
    (k : (Over.map a).obj T ⟶ acyclicHilbertTest f d) : T ⟶ acyclicHilbertTest q d :=
  (acyclicHilbertDegreeEquiv q d (fixedBaseAmple f a hL) T).symm
    (acyclicDegreeFixedBaseEquiv f a d T (acyclicHilbertDegreeMap f d _ k))

/-- Classification returns exactly the transported full divisor, not just its class. -/
theorem acyclicHilbertFixedBaseParameter_divisor (T : Over (Spec (.of R')))
    (k : (Over.map a).obj T ⟶ acyclicHilbertTest f d) :
    acyclicHilbertDegreeMap q d T (acyclicHilbertFixedBaseParameter f a hL d T k) =
      acyclicDegreeFixedBaseEquiv f a d T (acyclicHilbertDegreeMap f d _ k) :=
  (acyclicHilbertDegreeEquiv q d (fixedBaseAmple f a hL) T).apply_symm_apply _

/-- The transported Hilbert parameter has the entire pulled-back original ideal. -/
theorem acyclicHilbertFixedBaseParameter_ideal (T : Over (Spec (.of R')))
    (k : (Over.map a).obj T ⟶ acyclicHilbertTest f d) :
    (acyclicHilbertParameterDivisor q d T
      (acyclicHilbertFixedBaseParameter f a hL d T k)).val.val =
        (acyclicHilbertParameterDivisor f d ((Over.map a).obj T) k).val.val.comap
          (relativeBaseChangeTotalIso f a T).hom := by
  have h := congrArg (fun D ↦ D.val.val.val)
    (acyclicHilbertFixedBaseParameter_divisor f a hL d T k)
  exact h.trans (acyclicDivisorFixedBaseChange_ideal f a T _)

/-- The constructed scheme isomorphism realizes this exact full-ideal parameter transport. -/
theorem acyclicHilbertFixedBaseIso_point (T : Over (Spec (.of R')))
    (k : T ⟶ (Over.pullback a).obj (acyclicHilbertTest f d)) :
    k ≫ (acyclicHilbertFixedBaseIso f a hL d).hom =
      acyclicHilbertFixedBaseParameter f a hL d T
        (((Over.mapPullbackAdj a).homEquiv T (acyclicHilbertTest f d)).symm k) := by
  have h := Yoneda.fullyFaithful.map_preimage
    (acyclicHilbertFixedBasePresheafIso f a hL d).hom
  exact congrArg (fun η ↦ η.app (op T) k) h

end FLT.Mazur.HilbertChart
