/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialFamilyRestriction

/-!
# Recovering global family parameters on arbitrary affine chart tests

If a chart point gives the actual extended quotient ideal, the global family
parameter restricts to that point. The prescribed basis is obtained from the
chart point itself, without a supplied basis or local inverse assumption.
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
variable (T : Type u) [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- A chart point of the actual extended ideal recovers the restricted global parameter. -/
theorem polynomialFamilyMorphism_affineTest (w : Fin d → MvPolynomial I R)
    (a : ChartRing R I d w →ₐ[R] T)
    (ha : pointIdeal R I d w a = J.map (MvPolynomial.map (algebraMap S T))) :
    Spec.map (CommRingCat.ofHom (algebraMap S T)) ≫ polynomialFamilyMorphism R I d S J hd =
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ polynomialHilbertChartι R I d w := by
  have hb : ∃ b : Module.Basis (Fin d) T
      (MvPolynomial I T ⧸ J.map (MvPolynomial.map (algebraMap S T))),
      ∀ i, polynomialBasisTuple R I d w T
        (J.map (MvPolynomial.map (algebraMap S T))) i = b i := by
    rw [← ha]
    exact (idealOfPoint R I d w a).property
  obtain ⟨l, hl, _⟩ := (polynomialBasisScheme_affineFactorization_iff R I d w S J T).mpr hb
  have hc := intrinsicChartMorphism_affineTest R I d w S J T hb l hl
  have he : (⟨J.map (MvPolynomial.map (algebraMap S T)), hb⟩ :
      PrescribedBasisIdeals R I d w T) = idealOfPoint R I d w a := Subtype.ext ha.symm
  rw [he, idealClassifyingMap_idealOfPoint] at hc
  have h := polynomialFamilyMorphism_schemeTest R I d S J hd w l
  rw [← Category.assoc, hl, ← Category.assoc, hc] at h
  exact h

end FLT.Mazur.HilbertChart
