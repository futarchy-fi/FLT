/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialFamilyAmbient
public import FLT.Mazur.PolynomialSpectrumBaseChangeCover

/-!
# Cartesian ambient maps of Hilbert parameters

Every parameter over the coefficient base gives the actual base change of
the global polynomial ambient space, with the original polynomial spectrum
as source.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (S : Type u) [CommRing S] [Algebra R S]

/-- Ambient lifting forms an actual cartesian square over the Hilbert parameter scheme. -/
theorem polynomialAmbientMap_isPullback
    (f : Spec (.of S) ⟶ polynomialHilbertScheme R I d)
    (hf : f ≫ polynomialHilbertStructure R I d =
      Spec.map (CommRingCat.ofHom (algebraMap R S))) :
    IsPullback (polynomialAmbientMap R I d S f hf)
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := S) (σ := I))))
      (pullback.fst _ _) f := by
  have h : IsPullback (Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := S) (σ := I))))
      (polynomialAmbientMap R I d S f hf ≫ pullback.snd _ _)
      (f ≫ polynomialHilbertStructure R I d)
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := R) (σ := I)))) := by
    rw [polynomialAmbientMap_snd, hf]
    exact polynomialSpectrum_isPullback R I S
  exact (h.of_bot (polynomialAmbientMap_fst R I d S f hf).symm
    (IsPullback.of_hasPullback _ _)).flip

end FLT.Mazur.HilbertChart
