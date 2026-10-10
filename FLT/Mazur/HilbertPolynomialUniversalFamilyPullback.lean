/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIdealSheafCoverComparison
public import FLT.Mazur.HilbertMonomialPrincipalSpecCover
public import FLT.Mazur.HilbertPolynomialFamilyPrincipal
public import FLT.Mazur.PolynomialSpectrumBaseChangeCover

/-!
# Recovering arbitrary finite flat polynomial quotient families

The ambient map of every finitely presented flat quotient of constant residue
rank pulls the global universal ideal back to the original full ideal. The
proof checks equality on the constructed principal monomial basis cover.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.BaseAdicThickening

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

/-- The actual polynomial localization spectra cover the ambient space of the family. -/
def polynomialFamilyAmbientCover : (Spec (.of (MvPolynomial I S))).OpenCover :=
  polynomialSpectrumCover S I
    (fun q : MonomialPrincipalIndex R I d S J ↦ Localization.Away q.2.val)
    (Scheme.Cover.exists_eq (monomialPrincipalSpecCover R I d S J hd))

/-- Every arbitrary affine quotient family is recovered from the global universal ideal. -/
theorem polynomialUniversalIdeal_familyPullback :
    (polynomialUniversalIdeal R I d).comap (polynomialFamilyAmbientMap R I d S J hd) =
      baseIdeal (.of (MvPolynomial I S)) J := by
  let C := polynomialFamilyAmbientCover R I d S J hd
  let _ : ∀ q, IsAffine (C.X q) := fun q ↦
    inferInstanceAs (IsAffine (Spec (.of (MvPolynomial I (Localization.Away q.2.val)))))
  apply idealSheaf_ext_of_affineCover C
  intro q
  change ((polynomialUniversalIdeal R I d).comap
    (polynomialFamilyAmbientMap R I d S J hd)).comap
      (Spec.map (CommRingCat.ofHom
        (MvPolynomial.map (algebraMap S (Localization.Away q.2.val))))) =
    (baseIdeal (.of (MvPolynomial I S)) J).comap
      (Spec.map (CommRingCat.ofHom
        (MvPolynomial.map (algebraMap S (Localization.Away q.2.val)))))
  rw [baseIdeal_comap_specMap]
  exact polynomialUniversalIdeal_principalPullback R I d S J hd
    (fun i ↦ MvPolynomial.monomial (q.1 i) 1) q.2

end FLT.Mazur.HilbertChart
