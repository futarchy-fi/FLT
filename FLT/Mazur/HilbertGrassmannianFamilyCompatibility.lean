/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertGrassmannianSchemeTest
public import FLT.Mazur.HilbertPolynomialSchemeClassification

/-!
# Recovery of full families through the global Grassmannian morphism

The global morphism gives exactly the original bounded-family construction
on every affine family. For arbitrary scheme families, equality after this
morphism forces equality of the entire original ideal sheaves.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
open GrassmannianChart FLT.Mazur.FCurve
set_option backward.isDefEq.respectTransparency false
universe u
variable (R I : Type u) [CommRing R] (d : ℕ)
variable {ι κ : Type u} [Fintype ι] [Fintype κ]
  (b : Module.Basis ι R (MvPolynomial.restrictTotalDegree I R (d + 1)))
  (hκ : Fintype.card κ = Fintype.card ι - d)
variable (S : Type u) [CommRing S] [Algebra R S]

/-- Replacing an ideal by a proved equal ideal preserves the actual family morphism. -/
theorem finiteFlatHilbertClassifyingMap_congr (J K : Ideal (MvPolynomial I S))
    [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]
    [Module.Flat S (MvPolynomial I S ⧸ J)]
    [Module.FinitePresentation S (MvPolynomial I S ⧸ K)]
    [Module.Flat S (MvPolynomial I S ⧸ K)]
    (hd : ∀ p : PrimeSpectrum S, Module.finrank p.asIdeal.ResidueField
      (MvPolynomial I p.asIdeal.ResidueField ⧸
        J.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d)
    (he : ∀ p : PrimeSpectrum S, Module.finrank p.asIdeal.ResidueField
      (MvPolynomial I p.asIdeal.ResidueField ⧸
        K.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d)
    (h : J = K) :
    finiteFlatHilbertClassifyingMap R S I J d hd b hκ =
      finiteFlatHilbertClassifyingMap R S I K d he b hκ := by
  subst K
  rfl

/-- Classifying an affine family and then applying the global map retains that exact family. -/
theorem hilbertGrassmannianMap_family (J : Ideal (MvPolynomial I S))
    [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]
    [Module.Flat S (MvPolynomial I S ⧸ J)]
    (hd : ∀ p : PrimeSpectrum S, Module.finrank p.asIdeal.ResidueField
      (MvPolynomial I p.asIdeal.ResidueField ⧸
        J.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d) :
    polynomialFamilyMorphism R I d S J hd ≫ hilbertGrassmannianMap R I d b hκ =
      finiteFlatHilbertClassifyingMap R S I J d hd b hκ := by
  rw [hilbertGrassmannianMap_affineTest R I d b hκ S _
    (polynomialFamilyMorphism_over R I d S J hd)]
  exact finiteFlatHilbertClassifyingMap_congr R I d b hκ S _ J _ hd
    (polynomialParameterIdeal_family R I d S J hd)

/-- Arbitrary scheme families are determined by their global Grassmannian morphisms. -/
theorem hilbertGrassmannianMap_schemeFamily_injective
    {X : Scheme.{u}} (s : X ⟶ Spec (.of R))
    (J K : (polynomialRelativeAmbient R I s).IdealSheafData)
    (hJ : FiniteLocallyFreeDegree (J.subschemeι ≫ pullback.fst _ _) d)
    (hK : FiniteLocallyFreeDegree (K.subschemeι ≫ pullback.fst _ _) d)
    (h : polynomialSchemeFamilyMorphism R I d s J hJ ≫
        hilbertGrassmannianMap R I d b hκ =
      polynomialSchemeFamilyMorphism R I d s K hK ≫ hilbertGrassmannianMap R I d b hκ) :
    J = K := by
  have he : (⟨J, hJ⟩ : PolynomialSchemeFamilies R I d s) = ⟨K, hK⟩ := by
    apply (polynomialSchemeClassification R I d s).symm.injective
    apply Subtype.ext
    exact hilbertGrassmannianMap_cancel R I d b hκ _ _ h
  exact congrArg Subtype.val he

end FLT.Mazur.HilbertChart
