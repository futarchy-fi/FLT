/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialFamilyMorphism
public import FLT.Mazur.HilbertPolynomialSchemeOver

/-!
# Testing the global family parameter on every intrinsic chart

Pulling back the monomial cover shows that the global parameter recovers every
prescribed polynomial tuple parameter, even on nonaffine tests. The resulting
family morphism respects the original coefficient base.
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
variable (hd : ∀ p : PrimeSpectrum S, Module.finrank p.asIdeal.ResidueField
  (MvPolynomial I p.asIdeal.ResidueField ⧸
    J.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d)

/-- Every intrinsic scheme test recovers its actual polynomial tuple parameter globally. -/
theorem polynomialFamilyMorphism_schemeTest (w : Fin d → MvPolynomial I R)
    {X : Scheme.{u}} (f : X ⟶ polynomialBasisScheme R I d w S J) :
    f ≫ Scheme.Opens.ι (X := Spec (.of S)) (polynomialBasisOpen R I d w S J) ≫
        polynomialFamilyMorphism R I d S J hd =
      f ≫ intrinsicChartMorphism R I d w S J ≫ polynomialHilbertChartι R I d w := by
  let C := monomialBasisSchemeCover R I S J d hd
  let a := f ≫ Scheme.Opens.ι (X := Spec (.of S)) (polynomialBasisOpen R I d w S J)
  apply Scheme.Cover.hom_ext (C.pullback₁ a)
  intro m
  have h := intrinsicChartMorphism_glued_agree R I d S J w
    (fun i ↦ MvPolynomial.monomial (m i) 1)
    (pullback.fst a (C.f m) ≫ f) (pullback.snd a (C.f m))
    (by
      rw [Category.assoc]
      change pullback.fst a (C.f m) ≫ a = pullback.snd a (C.f m) ≫ C.f m
      exact pullback.condition)
  change pullback.fst a (C.f m) ≫ a ≫ polynomialFamilyMorphism R I d S J hd =
    pullback.fst a (C.f m) ≫ f ≫ intrinsicChartMorphism R I d w S J ≫
      polynomialHilbertChartι R I d w
  rw [← Category.assoc, pullback.condition, Category.assoc,
    polynomialFamilyMorphism_restrict]
  simpa only [Category.assoc] using h.symm

/-- The global family parameter respects the original coefficient base. -/
theorem polynomialFamilyMorphism_over :
    polynomialFamilyMorphism R I d S J hd ≫ polynomialHilbertStructure R I d =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  apply (monomialBasisSchemeCover R I S J d hd).hom_ext
  intro m
  rw [← Category.assoc, polynomialFamilyMorphism_restrict, Category.assoc,
    polynomialHilbertChartι_over, intrinsicChartMorphism_over]
  rfl

end FLT.Mazur.HilbertChart
