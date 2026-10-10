/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialParameterInverse

/-!
# Affine representation of finite flat polynomial quotient families

The glued Hilbert scheme classifies all finitely presented flat polynomial
quotients of constant residue rank. The equivalence uses actual quotient
ideals and arbitrary scheme morphisms over the coefficient base. Both inverse
laws are proved, with no choice of basis in the family data.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

/-- Actual finite flat polynomial quotient families of prescribed residue rank. -/
def PolynomialQuotientFamilies (I : Type u) (d : ℕ) (S : Type u) [CommRing S] :=
  { J : Ideal (MvPolynomial I S) //
    Module.FinitePresentation S (MvPolynomial I S ⧸ J) ∧
    Module.Flat S (MvPolynomial I S ⧸ J) ∧
    ∀ p : PrimeSpectrum S, Module.finrank p.asIdeal.ResidueField
      (MvPolynomial I p.asIdeal.ResidueField ⧸
        J.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d }

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (S : Type u) [CommRing S] [Algebra R S]

/-- All affine Hilbert parameters over the original coefficient base. -/
def PolynomialHilbertParameters :=
  { f : Spec (.of S) ⟶ polynomialHilbertScheme R I d //
    f ≫ polynomialHilbertStructure R I d = Spec.map (CommRingCat.ofHom (algebraMap R S)) }

/-- The actual quotient family of an arbitrary affine Hilbert parameter. -/
def polynomialParameterFamily (f : PolynomialHilbertParameters R I d S) :
    PolynomialQuotientFamilies I d S :=
  ⟨polynomialParameterIdeal R I d S f.val f.property,
    polynomialParameterIdeal_finitePresentation R I d S f.val f.property,
    polynomialParameterIdeal_flat R I d S f.val f.property,
    polynomialParameterIdeal_residueRank R I d S f.val f.property⟩

/-- Classify an actual quotient family by its global parameter, without choosing a basis. -/
def polynomialQuotientParameter (J : PolynomialQuotientFamilies I d S) :
    PolynomialHilbertParameters R I d S := by
  let _ := J.property.1
  let _ := J.property.2.1
  exact ⟨polynomialFamilyMorphism R I d S J.val J.property.2.2,
    polynomialFamilyMorphism_over R I d S J.val J.property.2.2⟩

/-- Pulling back the universal quotient after classifying returns the entire supplied family. -/
theorem polynomialParameterFamily_quotientParameter (J : PolynomialQuotientFamilies I d S) :
    polynomialParameterFamily R I d S (polynomialQuotientParameter R I d S J) = J := by
  let _ := J.property.1
  let _ := J.property.2.1
  apply Subtype.ext
  exact polynomialParameterIdeal_family R I d S J.val J.property.2.2

/-- Classifying the pulled-back quotient returns every original affine parameter. -/
theorem polynomialQuotientParameter_parameterFamily (f : PolynomialHilbertParameters R I d S) :
    polynomialQuotientParameter R I d S (polynomialParameterFamily R I d S f) = f := by
  apply Subtype.ext
  exact polynomialParameterClassifyingMorphism_eq R I d S f.val f.property

/-- The affine representing equivalence for the actual glued polynomial Hilbert scheme. -/
def polynomialAffineClassification :
    PolynomialHilbertParameters R I d S ≃ PolynomialQuotientFamilies I d S where
  toFun := polynomialParameterFamily R I d S
  invFun := polynomialQuotientParameter R I d S
  left_inv := polynomialQuotientParameter_parameterFamily R I d S
  right_inv := polynomialParameterFamily_quotientParameter R I d S

/-- The equivalence sends a parameter to the full coordinate ideal of its universal pullback. -/
theorem polynomialAffineClassification_ideal (f : PolynomialHilbertParameters R I d S) :
    (polynomialAffineClassification R I d S f).val =
      polynomialParameterIdeal R I d S f.val f.property := rfl

/-- The inverse equivalence has the original global family morphism as its underlying map. -/
theorem polynomialAffineClassification_symm_morphism (J : PolynomialQuotientFamilies I d S) :
    let _ := J.property.1
    let _ := J.property.2.1
    ((polynomialAffineClassification R I d S).symm J).val =
      polynomialFamilyMorphism R I d S J.val J.property.2.2 := rfl

end FLT.Mazur.HilbertChart
