/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialChartGluing
public import FLT.Mazur.HilbertMonomialChartCover

/-!
# A classifying morphism for arbitrary finite flat polynomial quotient families

The intrinsic parameters agree in the glued scheme on every common test.
The monomial basis cover therefore constructs a morphism from the entire
base, with no chosen global quotient basis and no section-sum hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (S : Type u) [CommRing S] [Algebra R S] (J : Ideal (MvPolynomial I S))
variable [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]
variable [Module.Flat S (MvPolynomial I S ⧸ J)]

/-- Intrinsic parameters for the same scheme test agree in the actual glued scheme. -/
theorem intrinsicChartMorphism_glued_agree (w v : Fin d → MvPolynomial I R)
    {X : Scheme.{u}} (f : X ⟶ polynomialBasisScheme R I d w S J)
    (g : X ⟶ polynomialBasisScheme R I d v S J)
    (h : f ≫ Scheme.Opens.ι (X := Spec (.of S)) (polynomialBasisOpen R I d w S J) =
      g ≫ Scheme.Opens.ι (X := Spec (.of S)) (polynomialBasisOpen R I d v S J)) :
    f ≫ intrinsicChartMorphism R I d w S J ≫ polynomialHilbertChartι R I d w =
      g ≫ intrinsicChartMorphism R I d v S J ≫ polynomialHilbertChartι R I d v := by
  rw [← Category.assoc, ← intrinsicTupleComparison_ι R I d w v S J f g h,
    Category.assoc, ← polynomialHilbertChartι_transition, ← Category.assoc,
    intrinsicTupleComparison_transition, Category.assoc]

variable (hd : ∀ p : PrimeSpectrum S, Module.finrank p.asIdeal.ResidueField
  (MvPolynomial I p.asIdeal.ResidueField ⧸
    J.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d)

/-- The monomial chart parameters satisfy the actual pullback compatibility for gluing. -/
theorem monomialFamilyMorphism_agree (m n : Fin d → (I →₀ ℕ)) :
    pullback.fst ((monomialBasisSchemeCover R I S J d hd).f m)
        ((monomialBasisSchemeCover R I S J d hd).f n) ≫
      intrinsicChartMorphism R I d (fun i ↦ MvPolynomial.monomial (m i) 1) S J ≫
        polynomialHilbertChartι R I d (fun i ↦ MvPolynomial.monomial (m i) 1) =
    pullback.snd ((monomialBasisSchemeCover R I S J d hd).f m)
        ((monomialBasisSchemeCover R I S J d hd).f n) ≫
      intrinsicChartMorphism R I d (fun i ↦ MvPolynomial.monomial (n i) 1) S J ≫
        polynomialHilbertChartι R I d (fun i ↦ MvPolynomial.monomial (n i) 1) :=
  intrinsicChartMorphism_glued_agree R I d S J _ _ _ _ pullback.condition

/-- The actual global parameter of a finite flat family of polynomial quotients. -/
def polynomialFamilyMorphism : Spec (.of S) ⟶ polynomialHilbertScheme R I d :=
  (monomialBasisSchemeCover R I S J d hd).glueMorphisms
    (fun m ↦ intrinsicChartMorphism R I d (fun i ↦ MvPolynomial.monomial (m i) 1) S J ≫
      polynomialHilbertChartι R I d (fun i ↦ MvPolynomial.monomial (m i) 1))
    (monomialFamilyMorphism_agree R I d S J hd)

/-- The global parameter restricts to the original intrinsic monomial chart parameter. -/
theorem polynomialFamilyMorphism_restrict (m : Fin d → (I →₀ ℕ)) :
    (monomialBasisSchemeCover R I S J d hd).f m ≫ polynomialFamilyMorphism R I d S J hd =
      intrinsicChartMorphism R I d (fun i ↦ MvPolynomial.monomial (m i) 1) S J ≫
        polynomialHilbertChartι R I d (fun i ↦ MvPolynomial.monomial (m i) 1) :=
  (monomialBasisSchemeCover R I S J d hd).ι_glueMorphisms _ _ m

/-- The local ideal-classifying parameters uniquely determine the global morphism. -/
theorem polynomialFamilyMorphism_unique (f : Spec (.of S) ⟶ polynomialHilbertScheme R I d)
    (hf : ∀ m : Fin d → (I →₀ ℕ),
      (monomialBasisSchemeCover R I S J d hd).f m ≫ f =
        intrinsicChartMorphism R I d (fun i ↦ MvPolynomial.monomial (m i) 1) S J ≫
          polynomialHilbertChartι R I d (fun i ↦ MvPolynomial.monomial (m i) 1)) :
    f = polynomialFamilyMorphism R I d S J hd := by
  apply (monomialBasisSchemeCover R I S J d hd).hom_ext
  intro m
  rw [hf, polynomialFamilyMorphism_restrict]

end FLT.Mazur.HilbertChart
