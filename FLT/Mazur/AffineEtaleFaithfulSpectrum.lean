/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineEtaleFaithfulNeighborhood
public import FLT.Mazur.AffineBaseSectionAlgebra

/-!
# A constructed faithfully flat translation base over a localized coefficient ring

The actual principal base open is identified with its section spectrum. The
restricted original translation is affine, étale and surjective over that
spectrum. Its coefficients are faithfully flat, with the original base square.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineEtaleFaithfulNeighborhood
variable {V S : Scheme.{0}} (g : V ⟶ S) [IsAffine S] [Etale g]

/-- The actual coefficient ring of the constructed principal base open. -/
abbrev BaseRing (x : V) := Γ((baseOpen g x).toScheme, ⊤)

/-- The new affine base retains its original open map into the old base. -/
def spectrumBase (x : V) : Spec (.of (BaseRing g x)) ⟶ S :=
  (baseOpen g x).toScheme.isoSpec.inv ≫ (baseOpen g x).ι

instance spectrumBase_isOpenImmersion (x : V) : IsOpenImmersion (spectrumBase g x) := by
  unfold spectrumBase
  infer_instance

/-- The restricted original translation, now over the constructed coefficient spectrum. -/
def spectrumMap (x : V) : (sourceOpen g x).toScheme ⟶ Spec (.of (BaseRing g x)) :=
  map g x ≫ (baseOpen g x).toScheme.isoSpec.hom

instance spectrumMap_etale (x : V) : Etale (spectrumMap g x) := by
  unfold spectrumMap
  infer_instance

instance spectrumMap_surjective (x : V) : Surjective (spectrumMap g x) := by
  unfold spectrumMap
  infer_instance

/-- The localized translation retains the original structural morphism. -/
@[reassoc]
theorem spectrumMap_base (x : V) :
    spectrumMap g x ≫ spectrumBase g x = (sourceOpen g x).ι ≫ g := by
  simp only [spectrumMap, spectrumBase, Category.assoc, Iso.hom_inv_id_assoc, map_ι]

/-- The new spectrum square is the actual base change of the original translation. -/
theorem spectrum_isPullback (x : V) :
    IsPullback (sourceOpen g x).ι (spectrumMap g x) g (spectrumBase g x) := by
  apply (isPullback g x).of_iso (Iso.refl _) (Iso.refl _)
    (baseOpen g x).toScheme.isoSpec (Iso.refl _)
  · simp
  · simp [spectrumMap]
  · simp
  · simp [spectrumBase]

variable [IsAffine V]

/-- Faithful flatness of the actual localized section map follows from geometric coverage. -/
theorem map_faithfullyFlat (x : V) : (map g x).appTop.hom.FaithfullyFlat :=
  (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine (map g x)).mp
    ⟨inferInstance, inferInstance⟩

/-- The spectrum map has a faithfully flat original structural coefficient homomorphism. -/
theorem spectrumMap_faithfullyFlat (x : V) :
    (Approximation.affineBaseSectionMap (spectrumMap g x)).FaithfullyFlat := by
  change ((spectrumMap g x).appTop.hom.comp
    (Scheme.ΓSpecIso (.of (BaseRing g x))).inv.hom).FaithfullyFlat
  apply RingHom.FaithfullyFlat.stableUnderComposition
  · exact RingHom.FaithfullyFlat.of_bijective
      (Scheme.ΓSpecIso (.of (BaseRing g x))).symm.commRingCatIsoToRingEquiv.bijective
  · exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine
      (spectrumMap g x)).mp ⟨inferInstance, inferInstance⟩

end FLT.Mazur.AffineEtaleFaithfulNeighborhood
