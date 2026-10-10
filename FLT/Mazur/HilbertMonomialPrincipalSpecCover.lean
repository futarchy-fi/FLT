/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertMonomialChartCover

/-!
# A monomial basis cover by actual localization spectra

Replace each principal open in the monomial basis cover by its localization
spectrum. This retains the explicit quotient ideal and classifying parameter.
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

/-- Indices specifying a monomial basis and a principal neighborhood carrying that basis. -/
def MonomialPrincipalIndex := Σ m : Fin d → (I →₀ ℕ),
  PolynomialBasisNeighborhoods R I d (fun i ↦ MvPolynomial.monomial (m i) 1) S J

/-- The monomial principal cover expressed in its actual localization coordinate rings. -/
def monomialPrincipalSpecCover : (Spec (.of S)).OpenCover where
  I₀ := MonomialPrincipalIndex R I d S J
  X q := Spec (.of (Localization.Away q.2.val))
  f q := Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away q.2.val)))
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun p ↦ ?_, fun q ↦ inferInstance⟩
    obtain ⟨m, hm⟩ := exists_monomial_basisOpen R I S J p d (hd p)
    obtain ⟨r, hr⟩ := exists_polynomialBasisNeighborhood R I d
      (fun i ↦ MvPolynomial.monomial (m i) 1) S J p hm
    refine ⟨⟨m, r⟩, (basicOpenIsoSpecAway (R := .of S) r.val).hom ⟨p, hr⟩, ?_⟩
    exact congrArg (fun f ↦ f ⟨p, hr⟩)
      (basicOpenIsoSpecAway_hom_SpecMap (R := .of S) r.val)

end FLT.Mazur.HilbertChart
