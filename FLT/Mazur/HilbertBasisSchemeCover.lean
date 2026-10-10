/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialBasisCover
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# The scheme cover of the intrinsic polynomial basis locus

The actual principal basis neighborhoods form a scheme open cover. Their
classifying parameters give morphisms to the spectrum of the Hilbert chart ring.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Type u) (d : ℕ)
variable (w : Fin d → MvPolynomial I R)
variable (S : Type u) [CommRing S] [Algebra R S] (J : Ideal (MvPolynomial I S))
variable [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]

/-- The actual open subscheme on which the prescribed polynomials form a basis. -/
def polynomialBasisScheme : Scheme :=
  Scheme.Opens.toScheme (X := Spec (.of S)) (polynomialBasisOpen R I d w S J)


/-- The constructed principal basis neighborhoods cover the actual open subscheme. -/
def polynomialBasisSchemeCover : (polynomialBasisScheme R I d w S J).OpenCover where
  I₀ := PolynomialBasisNeighborhoods R I d w S J
  X r := Scheme.Opens.toScheme (X := Spec (.of S)) (PrimeSpectrum.basicOpen r.val)
  f r := (Spec (.of S)).homOfLE (neighborhood_basicOpen_le R I d w S J r)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, ?_⟩
    · obtain ⟨r, hr⟩ := exists_polynomialBasisNeighborhood R I d w S J x.1 x.2
      refine ⟨r, ⟨x.1, hr⟩, ?_⟩
      apply Subtype.ext
      exact Scheme.homOfLE_apply (neighborhood_basicOpen_le R I d w S J r) ⟨x.1, hr⟩
    · intro r
      change IsOpenImmersion ((Spec (.of S)).homOfLE
        (neighborhood_basicOpen_le R I d w S J r))
      infer_instance

/-- The actual local chart morphism induced by the ideal-classifying parameter. -/
def neighborhoodChartMorphism (r : PolynomialBasisNeighborhoods R I d w S J) :
    (polynomialBasisSchemeCover R I d w S J).X r ⟶ Spec (.of (ChartRing R I d w)) :=
  (basicOpenIsoSpecAway (R := .of S) r.val).hom ≫
    Spec.map (CommRingCat.ofHom (neighborhoodClassifyingMap R I d w S J r).toRingHom)

/-- Returning to the localized affine model recovers exactly the classifying ring map. -/
theorem neighborhoodChartMorphism_affine (r : PolynomialBasisNeighborhoods R I d w S J) :
    (basicOpenIsoSpecAway (R := .of S) r.val).inv ≫
      neighborhoodChartMorphism R I d w S J r =
    Spec.map (CommRingCat.ofHom (neighborhoodClassifyingMap R I d w S J r).toRingHom) := by
  rw [neighborhoodChartMorphism, Iso.inv_hom_id_assoc]

end FLT.Mazur.HilbertChart
