/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialAffineClassification
public import FLT.Mazur.HilbertPolynomialFamilyBaseChangeRank

/-!
# Naturality of affine polynomial Hilbert classification

Arbitrary coefficient extension acts on actual ideals by ideal extension and
on parameters by composition of spectra. The representing equivalence and
its inverse commute with those operations.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (S : Type u) [CommRing S] [Algebra R S]
variable (T : Type u) [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- Scalar extension of an actual quotient family retains finite presentation, flatness and rank. -/
def polynomialQuotientFamilyBaseChange (J : PolynomialQuotientFamilies I d S) :
    PolynomialQuotientFamilies I d T := by
  let _ := J.property.1
  let _ := J.property.2.1
  exact ⟨J.val.map (MvPolynomial.map (algebraMap S T)),
    polynomialQuotient_finitePresentation_baseChange I S J.val T,
    polynomialQuotient_flat_baseChange I S J.val T,
    polynomialQuotient_residueRank_baseChange I S J.val T d J.property.2.2⟩

/-- The actual parameter after scalar extension is composition with the coefficient spectrum map. -/
def polynomialHilbertParameterBaseChange (f : PolynomialHilbertParameters R I d S) :
    PolynomialHilbertParameters R I d T :=
  ⟨Spec.map (CommRingCat.ofHom (algebraMap S T)) ≫ f.val, by
    rw [Category.assoc, f.property, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (IsScalarTower.algebraMap_eq R S T).symm⟩

/-- The representing equivalence commutes with every scalar extension of coefficient rings. -/
theorem polynomialAffineClassification_natural (f : PolynomialHilbertParameters R I d S) :
    polynomialAffineClassification R I d T
        (polynomialHilbertParameterBaseChange R I d S T f) =
      polynomialQuotientFamilyBaseChange I d S T (polynomialAffineClassification R I d S f) := by
  apply Subtype.ext
  exact polynomialParameterIdeal_baseChange R I d S f.val f.property T
    (IsScalarTower.toAlgHom R S T) _
      (polynomialHilbertParameterBaseChange R I d S T f).property rfl

/-- Inverse classification commutes with scalar extension as actual parameter morphisms. -/
theorem polynomialAffineClassification_symm_natural (J : PolynomialQuotientFamilies I d S) :
    (polynomialAffineClassification R I d T).symm (polynomialQuotientFamilyBaseChange I d S T J) =
      polynomialHilbertParameterBaseChange R I d S T
        ((polynomialAffineClassification R I d S).symm J) := by
  apply (polynomialAffineClassification R I d T).injective
  rw [Equiv.apply_symm_apply, polynomialAffineClassification_natural, Equiv.apply_symm_apply]

end FLT.Mazur.HilbertChart
