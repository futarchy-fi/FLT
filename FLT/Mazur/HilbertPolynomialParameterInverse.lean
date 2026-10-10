/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialParameterRecovery

/-!
# The global inverse law for arbitrary affine Hilbert parameters

The pulled-back Hilbert chart cover detects equality of parameter morphisms.
Reclassifying the full pulled-back polynomial ideal therefore recovers the
original arbitrary parameter over the coefficient base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (S : Type u) [CommRing S] [Algebra R S]
variable (f : Spec (.of S) ⟶ polynomialHilbertScheme R I d)
variable (hf : f ≫ polynomialHilbertStructure R I d =
  Spec.map (CommRingCat.ofHom (algebraMap R S)))

/-- Classifying the actual quotient of any affine parameter returns that same parameter. -/
theorem polynomialParameterClassifyingMorphism_eq :
    polynomialParameterClassifyingMorphism R I d S f hf = f := by
  apply Scheme.Cover.hom_ext ((polynomialHilbertSchemeCover R I d).pullback₁ f)
  intro w
  exact polynomialParameterClassifyingMorphism_schemeTest R I d S f hf w
    (pullback.fst f (polynomialHilbertChartι R I d w))
    (pullback.snd f (polynomialHilbertChartι R I d w)) pullback.condition

/-- Arbitrary parameters over the base are determined by their entire pulled-back ideals. -/
theorem polynomialParameterIdeal_injective
    (g : Spec (.of S) ⟶ polynomialHilbertScheme R I d)
    (hg : g ≫ polynomialHilbertStructure R I d =
      Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (h : polynomialParameterIdeal R I d S f hf = polynomialParameterIdeal R I d S g hg) :
    f = g := by
  rw [← polynomialParameterClassifyingMorphism_eq R I d S f hf,
    ← polynomialParameterClassifyingMorphism_eq R I d S g hg]
  unfold polynomialParameterClassifyingMorphism
  congr 1

end FLT.Mazur.HilbertChart
