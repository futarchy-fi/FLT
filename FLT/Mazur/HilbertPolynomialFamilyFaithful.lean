/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialUniversalFamilyPullback

/-!
# Distinguishing affine families by their Hilbert parameters

Equality of the constructed global parameters forces equality of the entire
original polynomial ideals, including nonreduced structure.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.BaseAdicThickening

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

/-- The actual ideal sheaf of an affine coordinate ideal remembers the entire ideal. -/
theorem polynomialBaseIdeal_injective (A : CommRingCat.{u}) :
    Function.Injective (baseIdeal A) := by
  intro J K h
  have he := congrArg (fun L : (Spec A).IdealSheafData ↦
    L.ideal ⟨⊤, isAffineOpen_top _⟩) h
  rw [baseIdeal_top, baseIdeal_top] at he
  apply_fun Ideal.map (Scheme.ΓSpecIso A).hom.hom at he
  simpa only [Ideal.map_map, ← CommRingCat.hom_comp, Iso.inv_hom_id,
    CommRingCat.hom_id, Ideal.map_id] using he

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (S : Type u) [CommRing S] [Algebra R S]
variable (J K : Ideal (MvPolynomial I S))
variable [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]
variable [Module.Flat S (MvPolynomial I S ⧸ J)]
variable [Module.FinitePresentation S (MvPolynomial I S ⧸ K)]
variable [Module.Flat S (MvPolynomial I S ⧸ K)]
variable (hJ : ∀ p : PrimeSpectrum S, Module.finrank p.asIdeal.ResidueField
  (MvPolynomial I p.asIdeal.ResidueField ⧸
    J.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d)
variable (hK : ∀ p : PrimeSpectrum S, Module.finrank p.asIdeal.ResidueField
  (MvPolynomial I p.asIdeal.ResidueField ⧸
    K.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d)

/-- Equal global classifying parameters imply equal actual polynomial quotient ideals. -/
theorem polynomialFamilyMorphism_eq_implies_ideal_eq
    (h : polynomialFamilyMorphism R I d S J hJ = polynomialFamilyMorphism R I d S K hK) :
    J = K := by
  have ha : polynomialFamilyAmbientMap R I d S J hJ =
      polynomialFamilyAmbientMap R I d S K hK := by
    simp only [polynomialFamilyAmbientMap, h]
  apply polynomialBaseIdeal_injective (.of (MvPolynomial I S))
  rw [← polynomialUniversalIdeal_familyPullback R I d S J hJ,
    ← polynomialUniversalIdeal_familyPullback R I d S K hK, ha]

end FLT.Mazur.HilbertChart
