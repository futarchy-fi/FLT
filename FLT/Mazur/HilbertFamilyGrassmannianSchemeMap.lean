/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertFamilyGrassmannianParameter
public import FLT.Mazur.HilbertBoundedPolynomialBaseChange
public import FLT.Mazur.GrassmannianAmbientPointTransport
public import FLT.Mazur.GrassmannianAmbientClassifyingInjective

/-!
# Actual Grassmannian scheme morphisms of finite flat Hilbert families

Use the original bounded polynomial ambient over the original base ring.
The resulting scheme morphism determines the entire family ideal, including
all equations beyond the degree truncation. Immersion remains further work.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace FLT.Mazur.HilbertChart
open GrassmannianChart
universe u
variable (R S I : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (J : Ideal (MvPolynomial I S)) (d : ℕ)
  [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]
  [Module.Flat S (MvPolynomial I S ⧸ J)]
  (hd : ∀ p : PrimeSpectrum S, Module.finrank p.asIdeal.ResidueField
    (MvPolynomial I p.asIdeal.ResidueField ⧸
      J.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d)

/-- The full family parameter in the original base's bounded ambient coordinates. -/
def finiteFlatHilbertAmbientPoint :
    Module.Grassmannian S (S ⊗[R] MvPolynomial.restrictTotalDegree I R (d + 1)) d :=
  ambientTransportPoint (boundedPolynomialBaseChangeEquiv R S I (d + 1)).symm
    (finiteFlatGrassmannianParameter S I J d hd)

/-- Membership retains exactly the original bounded relation, in the actual coefficient algebra. -/
theorem finiteFlatHilbertAmbientPoint_mem
    (x : S ⊗[R] MvPolynomial.restrictTotalDegree I R (d + 1)) :
    x ∈ (finiteFlatHilbertAmbientPoint R S I J d hd).toSubmodule ↔
      boundedPolynomialBaseChangeEquiv R S I (d + 1) x ∈
        boundedRelationKernel S I J (d + 1) := by
  exact ambientTransportPoint_mem (boundedPolynomialBaseChangeEquiv R S I (d + 1)).symm
    (finiteFlatGrassmannianParameter S I J d hd) x

variable {ι κ : Type u} [Fintype ι] [Fintype κ]
  (b : Module.Basis ι R (MvPolynomial.restrictTotalDegree I R (d + 1)))
  (hκ : Fintype.card κ = Fintype.card ι - d)

/-- A finite flat family constructs a genuine Grassmannian scheme morphism over its base. -/
def finiteFlatHilbertClassifyingMap :
    Spec (.of S) ⟶
      ambientGrassmannianScheme R (MvPolynomial.restrictTotalDegree I R (d + 1)) κ d :=
  ambientClassifyingMap b (finiteFlatHilbertAmbientPoint R S I J d hd) hκ

/-- The actual family morphism retains its original coefficient-algebra structure. -/
@[reassoc] theorem finiteFlatHilbertClassifyingMap_over :
    finiteFlatHilbertClassifyingMap R S I J d hd b hκ ≫
      ambientGrassmannianStructure R (MvPolynomial.restrictTotalDegree I R (d + 1)) κ d =
      Spec.algebraMap R S :=
  ambientClassifyingMap_over b (finiteFlatHilbertAmbientPoint R S I J d hd) hκ

variable (K : Ideal (MvPolynomial I S))
  [Module.FinitePresentation S (MvPolynomial I S ⧸ K)]
  [Module.Flat S (MvPolynomial I S ⧸ K)]
  (he : ∀ p : PrimeSpectrum S, Module.finrank p.asIdeal.ResidueField
    (MvPolynomial I p.asIdeal.ResidueField ⧸
      K.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d)

/-- Equal scheme morphisms force equality of the entire original family ideals. -/
theorem finiteFlatHilbertClassifyingMap_injective
    (h : finiteFlatHilbertClassifyingMap R S I J d hd b hκ =
      finiteFlatHilbertClassifyingMap R S I K d he b hκ) : J = K := by
  have hp : finiteFlatHilbertAmbientPoint R S I J d hd =
      finiteFlatHilbertAmbientPoint R S I K d he :=
    ambientClassifyingMap_injective b hκ h
  apply finiteFlatGrassmannianParameter_injective S I J d hd K he
  exact (ambientTransportPointEquiv
    (boundedPolynomialBaseChangeEquiv R S I (d + 1)).symm).injective hp

end FLT.Mazur.HilbertChart
