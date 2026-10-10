/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialAmbientNaturality
public import FLT.Mazur.HilbertPolynomialFamilyNaturality

/-!
# Naturality of the actual affine-family ambient morphism

Arbitrary scalar extension commutes with the constructed ambient family map.
Finite presentation, flatness and residue rank of the extended quotient are
proved from the original family, with no new extended-family hypotheses.
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

/-- The actual ambient map of the quotient family commutes with arbitrary scalar extension. -/
theorem polynomialFamilyAmbientMap_baseChange :
    Spec.map (CommRingCat.ofHom (MvPolynomial.map (algebraMap S T))) ≫
        polynomialFamilyAmbientMap R I d S J hd =
      polynomialFamilyAmbientMap R I d T (J.map (MvPolynomial.map (algebraMap S T)))
        (polynomialQuotient_residueRank_baseChange I S J T d hd) :=
  polynomialAmbientMap_baseChange R I d S _ (polynomialFamilyMorphism_over R I d S J hd)
    T (IsScalarTower.toAlgHom R S T) _ (polynomialFamilyMorphism_over R I d T _ _)
    (polynomialFamilyMorphism_baseChange R I d S J hd T)

end FLT.Mazur.HilbertChart
