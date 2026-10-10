/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIdealCoordinates
public import FLT.Mazur.HilbertPolynomialAmbientNaturality

/-!
# The actual polynomial ideal of an arbitrary Hilbert parameter

Pull back the global universal ideal along the parameter's ambient map and
take its affine coordinates. This construction requires no supplied basis
or finiteness hypothesis and commutes with every scalar extension.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.BaseAdicThickening

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (S : Type u) [CommRing S] [Algebra R S]
variable (f : Spec (.of S) ⟶ polynomialHilbertScheme R I d)
variable (hf : f ≫ polynomialHilbertStructure R I d =
  Spec.map (CommRingCat.ofHom (algebraMap R S)))

/-- The full polynomial ideal pulled back from an arbitrary parameter over the base. -/
def polynomialParameterIdeal : Ideal (MvPolynomial I S) :=
  coordinateIdeal (.of (MvPolynomial I S))
    ((polynomialUniversalIdeal R I d).comap (polynomialAmbientMap R I d S f hf))

/-- Sheafifying the parameter ideal recovers the actual universal pullback. -/
theorem polynomialParameterIdeal_sheaf :
    baseIdeal (.of (MvPolynomial I S)) (polynomialParameterIdeal R I d S f hf) =
      (polynomialUniversalIdeal R I d).comap (polynomialAmbientMap R I d S f hf) :=
  baseIdeal_coordinateIdeal _ _

/-- Pulling back after an arbitrary scalar extension extends the full polynomial ideal. -/
theorem polynomialParameterIdeal_baseChange
    (T : Type u) [CommRing T] [Algebra R T] (a : S →ₐ[R] T)
    (g : Spec (.of T) ⟶ polynomialHilbertScheme R I d)
    (hg : g ≫ polynomialHilbertStructure R I d =
      Spec.map (CommRingCat.ofHom (algebraMap R T)))
    (ha : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ f = g) :
    polynomialParameterIdeal R I d T g hg =
      (polynomialParameterIdeal R I d S f hf).map (MvPolynomial.map a.toRingHom) := by
  unfold polynomialParameterIdeal
  rw [← polynomialAmbientMap_baseChange R I d S f hf T a g hg ha,
    Scheme.IdealSheafData.comap_comp, coordinateIdeal_comap_specMap]
  rfl

/-- Recovering the ideal after classifying an affine quotient returns that entire ideal. -/
theorem polynomialParameterIdeal_family
    (J : Ideal (MvPolynomial I S))
    [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]
    [Module.Flat S (MvPolynomial I S ⧸ J)]
    (hd : ∀ p : PrimeSpectrum S, Module.finrank p.asIdeal.ResidueField
      (MvPolynomial I p.asIdeal.ResidueField ⧸
        J.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d) :
    polynomialParameterIdeal R I d S (polynomialFamilyMorphism R I d S J hd)
      (polynomialFamilyMorphism_over R I d S J hd) = J := by
  change coordinateIdeal _ ((polynomialUniversalIdeal R I d).comap
    (polynomialFamilyAmbientMap R I d S J hd)) = J
  rw [polynomialUniversalIdeal_familyPullback, coordinateIdeal_baseIdeal]

end FLT.Mazur.HilbertChart
