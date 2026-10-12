/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineEtaleFaithfulSpectrum
public import FLT.Mazur.AffineBaseSectionFunctor

/-!
# Original scalars on the constructed faithful translation neighborhoods

The new base coefficients are the actual principal localization. Over an
original finitely generated integer algebra they are still finitely generated,
so the localized base is eligible for the proper-family Hilbert constructions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineEtaleFaithfulNeighborhood
open Approximation
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {V : Scheme} (g : V ⟶ Spec (.of R)) [Etale g]

/-- The actual localized base coefficients retain the original R-algebra action. -/
@[instance_reducible]
def originalBaseAlgebra (x : V) : Algebra R (BaseRing g x) :=
  affineBaseSectionAlgebra (baseOpen g x).ι

/-- The new coefficient ring is the actual principal localization of base global sections. -/
theorem baseRing_isLocalization (x : V) :
    IsLocalization.Away (parameter g x) (BaseRing g x) := by
  change IsLocalization.Away (parameter g x)
    Γ(((Spec (.of R)).basicOpen (parameter g x)).toScheme, ⊤)
  infer_instance

/-- The constructed coefficient algebra has finite presentation over the original ring. -/
theorem originalBase_finitePresentation (x : V) :
    let _ := originalBaseAlgebra g x
    Algebra.FinitePresentation R (BaseRing g x) :=
  affineBaseSection_finitePresentation (baseOpen g x).ι

/-- Localizing the original finite-type integer base preserves that hypothesis. -/
instance baseRing_finiteType [Algebra.FiniteType ℤ R] (x : V) :
    Algebra.FiniteType ℤ (BaseRing g x) := by
  let _ := originalBaseAlgebra g x
  let _ : Algebra.FinitePresentation R (BaseRing g x) := originalBase_finitePresentation g x
  exact Algebra.FiniteType.trans (R := ℤ) (S := R) inferInstance inferInstance

/-- The new spectrum's base arrow is exactly the spectrum of the original scalar action. -/
theorem spectrumBase_eq_specMap (x : V) :
    let _ := originalBaseAlgebra g x
    spectrumBase g x = Spec.map (CommRingCat.ofHom (algebraMap R (BaseRing g x))) := by
  let _ := originalBaseAlgebra g x
  let _ : IsAffine (Over.mk (baseOpen g x).ι).left := base_affine g x
  dsimp only
  apply (cancel_epi (baseOpen g x).toScheme.isoSpec.hom).mp
  rw [spectrumBase, Iso.hom_inv_id_assoc]
  exact (affineBaseSectionsSpecIso_over R (Over.mk (baseOpen g x).ι)).symm

/-- The original restricted translation coefficients are faithfully flat over this new ring. -/
theorem sourceCoefficients_faithfullyFlat [IsAffine V] (x : V) :
    let _ := affineBaseSectionAlgebra (spectrumMap g x)
    Module.FaithfullyFlat (BaseRing g x) Γ((sourceOpen g x).toScheme, ⊤) := by
  let _ := affineBaseSectionAlgebra (spectrumMap g x)
  exact RingHom.faithfullyFlat_algebraMap_iff.mp (spectrumMap_faithfullyFlat g x)

/-- The localized translation coefficients are finitely presented over the new base ring. -/
theorem sourceCoefficients_finitePresentation [IsAffine V] (x : V) :
    let _ := affineBaseSectionAlgebra (spectrumMap g x)
    Algebra.FinitePresentation (BaseRing g x) Γ((sourceOpen g x).toScheme, ⊤) :=
  affineBaseSection_finitePresentation (spectrumMap g x)

end FLT.Mazur.AffineEtaleFaithfulNeighborhood
