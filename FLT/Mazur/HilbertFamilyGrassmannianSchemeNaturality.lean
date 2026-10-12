/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertFamilyAmbientPointNaturality
public import FLT.Mazur.GrassmannianAmbientClassifyingNaturality

/-!
# Scheme naturality of the full Hilbert family parameter

Every coefficient algebra map commutes with the actual Grassmannian scheme
morphism. The compatibility uses equality of the entire extended ideal.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
open GrassmannianChart
set_option backward.isDefEq.respectTransparency false
universe u
variable (R S T I : Type u) [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]
variable (J : Ideal (MvPolynomial I S)) (d : ℕ)
  [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]
  [Module.Flat S (MvPolynomial I S ⧸ J)]
  (hd : ∀ p : PrimeSpectrum S, Module.finrank p.asIdeal.ResidueField
    (MvPolynomial I p.asIdeal.ResidueField ⧸
      J.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d)
variable {ι κ : Type u} [Fintype ι] [Fintype κ]
  (b : Module.Basis ι R (MvPolynomial.restrictTotalDegree I R (d + 1)))
  (hκ : Fintype.card κ = Fintype.card ι - d)

section Tower
variable [Algebra S T] [IsScalarTower R S T]
local instance hilbertSchemeExtendedFinitePresentation : Module.FinitePresentation T
    (MvPolynomial I T ⧸ J.map (MvPolynomial.map (algebraMap S T))) :=
  polynomialQuotient_finitePresentation_baseChange I S J T
local instance hilbertSchemeExtendedFlat : Module.Flat T
    (MvPolynomial I T ⧸ J.map (MvPolynomial.map (algebraMap S T))) :=
  polynomialQuotient_flat_baseChange I S J T

/-- The actual family morphism commutes with arbitrary extension of its coefficient ring. -/
theorem finiteFlatHilbertClassifyingMap_baseChange :
    finiteFlatHilbertClassifyingMap R T I (J.map (MvPolynomial.map (algebraMap S T))) d
        (polynomialQuotient_residueRank_baseChange I S J T d hd) b hκ =
      Spec.algebraMap S T ≫ finiteFlatHilbertClassifyingMap R S I J d hd b hκ := by
  unfold finiteFlatHilbertClassifyingMap
  rw [← finiteFlatHilbertAmbientPoint_natural R S T I J d hd]
  exact ambientClassifyingMap_natural b _ hκ (IsScalarTower.toAlgHom R S T)

end Tower

/-- Equality of the full extended ideals gives naturality for every original algebra map. -/
theorem finiteFlatHilbertClassifyingMap_natural (f : S →ₐ[R] T)
    (K : Ideal (MvPolynomial I T))
    [Module.FinitePresentation T (MvPolynomial I T ⧸ K)]
    [Module.Flat T (MvPolynomial I T ⧸ K)]
    (he : ∀ p : PrimeSpectrum T, Module.finrank p.asIdeal.ResidueField
      (MvPolynomial I p.asIdeal.ResidueField ⧸
        K.map (MvPolynomial.map (algebraMap T p.asIdeal.ResidueField))) = d)
    (hK : J.map (MvPolynomial.map f.toRingHom) = K) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        finiteFlatHilbertClassifyingMap R S I J d hd b hκ =
      finiteFlatHilbertClassifyingMap R T I K d he b hκ := by
  algebraize [f.toRingHom]
  subst K
  exact (finiteFlatHilbertClassifyingMap_baseChange R S T I J d hd b hκ).symm

end FLT.Mazur.HilbertChart
