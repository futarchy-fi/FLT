/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialFamilyBaseChangeRank
public import FLT.Mazur.HilbertPolynomialFamilyRestriction

/-!
# Naturality of the global polynomial family morphism

Every scalar extension preserves the actual finite flat quotient and its
residue rank. On its intrinsic basis cover the two global morphisms agree by
the already constructed base-change map of intrinsic basis schemes.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (S : Type u) [CommRing S] [Algebra R S] (J : Ideal (MvPolynomial I S))
variable [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]
variable [Module.Flat S (MvPolynomial I S ⧸ J)]
variable (hd : ∀ p : PrimeSpectrum S, Module.finrank p.asIdeal.ResidueField
  (MvPolynomial I p.asIdeal.ResidueField ⧸
    J.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d)
variable (T : Type u) [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

local instance : Module.FinitePresentation T
    (MvPolynomial I T ⧸ J.map (MvPolynomial.map (algebraMap S T))) :=
  polynomialQuotient_finitePresentation_baseChange I S J T

local instance : Module.Flat T
    (MvPolynomial I T ⧸ J.map (MvPolynomial.map (algebraMap S T))) :=
  polynomialQuotient_flat_baseChange I S J T

/-- The global classifying morphism commutes with arbitrary scalar extension. -/
theorem polynomialFamilyMorphism_baseChange :
    Spec.map (CommRingCat.ofHom (algebraMap S T)) ≫ polynomialFamilyMorphism R I d S J hd =
      polynomialFamilyMorphism R I d T (J.map (MvPolynomial.map (algebraMap S T)))
        (polynomialQuotient_residueRank_baseChange I S J T d hd) := by
  apply polynomialFamilyMorphism_unique
  intro m
  let w : Fin d → MvPolynomial I R := fun i ↦ MvPolynomial.monomial (m i) 1
  have h := polynomialFamilyMorphism_schemeTest R I d S J hd w
    (polynomialBasisBaseChangeMorphism R I d w S J T)
  simp only [← Category.assoc] at h
  rw [intrinsicChartMorphism_baseChange] at h
  rw [polynomialBasisBaseChangeMorphism,
    Scheme.Hom.resLE_comp_ι, Category.assoc] at h
  exact h

end FLT.Mazur.HilbertChart
