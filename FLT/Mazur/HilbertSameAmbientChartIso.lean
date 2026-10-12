/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertCommonAmbientOverlap
public import FLT.Mazur.HilbertSupportOpenLattice

/-!
# Full Hilbert schemes of two presentations of the same ambient open

When two original quotient embeddings have the same image, the common support
opens are the whole Hilbert schemes. Their existing full-family comparison
therefore gives an isomorphism of the entire parameter schemes over the base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
set_option backward.isDefEq.respectTransparency false
universe u
variable (R I I' : Type u) [CommRing R] (d : ℕ)
  (K : Ideal (MvPolynomial I R)) (K' : Ideal (MvPolynomial I' R))
  {Z : Scheme.{u}} (z : Z ⟶ Spec (.of R))
  (i : Spec (.of (MvPolynomial I R ⧸ K)) ⟶ Z)
  (j : Spec (.of (MvPolynomial I' R ⧸ K')) ⟶ Z)
  [IsOpenImmersion i] [IsOpenImmersion j]
  (hi : i ≫ z = Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial I R ⧸ K))))
  (hj : j ≫ z = Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial I' R ⧸ K'))))
  (h : i.opensRange = j.opensRange)

/-- Support inside the image of the original chart imposes no restriction. -/
def hilbertOwnImageIso :
    (ambientHilbertSupportOpen R I d K (i ⁻¹ᵁ i.opensRange)).toScheme ≅
      ambientHilbertScheme R I d K :=
  (ambientHilbertScheme R I d K).isoOfEq
    (by rw [Scheme.Hom.preimage_opensRange, ambientHilbertSupportOpen_top]) ≪≫
      (ambientHilbertScheme R I d K).topIso

/-- The unrestricted image identification uses the original support inclusion. -/
theorem hilbertOwnImageIso_hom :
    (hilbertOwnImageIso R I d K i).hom =
      (ambientHilbertSupportOpen R I d K (i ⁻¹ᵁ i.opensRange)).ι := by
  simp only [hilbertOwnImageIso, Iso.trans_hom, Scheme.topIso_hom,
    Scheme.isoOfEq_hom_ι]

/-- Equal original chart images give an isomorphism of their full Hilbert schemes. -/
def sameAmbientHilbertIso : ambientHilbertScheme R I d K ≅
    ambientHilbertScheme R I' d K' :=
  (hilbertOwnImageIso R I d K i).symm ≪≫
    commonAmbientHilbertIso R I I' d K K' z i j hi hj i.opensRange le_rfl h.le ≪≫
      (ambientHilbertScheme R I' d K').isoOfEq (by rw [h]) ≪≫
        hilbertOwnImageIso R I' d K' j

/-- The entire parameter comparison preserves the original coefficient map. -/
theorem sameAmbientHilbertIso_over :
    (sameAmbientHilbertIso R I I' d K K' z i j hi hj h).hom ≫
      ambientHilbertStructure R I' d K' = ambientHilbertStructure R I d K := by
  apply (cancel_epi (hilbertOwnImageIso R I d K i).hom).mp
  simp only [sameAmbientHilbertIso, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc,
    reassoc_of% (hilbertOwnImageIso_hom R I' d K' j),
    Category.assoc, Scheme.isoOfEq_hom_ι_assoc]
  change (commonAmbientHilbertIso R I I' d K K' z i j hi hj _ _ _).hom ≫
    openAmbientHilbertStructure R I' d K' _ = _
  rw [commonAmbientHilbertIso_over, hilbertOwnImageIso_hom]
  rfl

end FLT.Mazur.HilbertChart
