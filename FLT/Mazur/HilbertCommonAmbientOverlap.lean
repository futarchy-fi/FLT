/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CommonAmbientOpenIso
public import FLT.Mazur.HilbertOpenOverlapCoherence

/-!
# Hilbert overlaps from actual affine charts of a shared ambient

Affine quotient charts embedded in the same scheme give canonical Hilbert
overlap isomorphisms on every common open. This constructs the pairwise
comparisons from the actual chart geometry, and proves their scheme-level
cocycle on every common triple open by full intrinsic-family classification.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.OpenIdealCover

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I I' I'' : Type u) [CommRing R] (d : ℕ)
variable (K : Ideal (MvPolynomial I R)) (K' : Ideal (MvPolynomial I' R))
variable (K'' : Ideal (MvPolynomial I'' R))
variable {Z : Scheme.{u}} (z : Z ⟶ Spec (.of R))
variable (i : Spec (.of (MvPolynomial I R ⧸ K)) ⟶ Z)
variable (j : Spec (.of (MvPolynomial I' R ⧸ K')) ⟶ Z)
variable (k : Spec (.of (MvPolynomial I'' R ⧸ K'')) ⟶ Z)
variable [IsOpenImmersion i] [IsOpenImmersion j] [IsOpenImmersion k]
variable (hi : i ≫ z = Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial I R ⧸ K))))
variable (hj : j ≫ z = Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial I' R ⧸ K'))))
variable (hk : k ≫ z = Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial I'' R ⧸ K''))))
variable (U : Z.Opens) (hU : U ≤ i.opensRange) (hV : U ≤ j.opensRange)

include hi hj in
/-- The canonical comparison of original common opens lies over the coefficient scheme. -/
theorem commonAmbientOpenIso_coefficient :
    (commonAmbientOpenIso i j U hU hV).hom ≫
        quotientOriginalOpenStructure R I' K' (j ⁻¹ᵁ U) =
      quotientOriginalOpenStructure R I K (i ⁻¹ᵁ U) := by
  unfold quotientOriginalOpenStructure
  rw [← hi, ← hj]
  exact commonAmbientOpenIso_over_assoc i j U hU hV z

/-- Actual charts of one ambient construct an isomorphism of their Hilbert common opens. -/
def commonAmbientHilbertIso :
    (ambientHilbertSupportOpen R I d K (i ⁻¹ᵁ U)).toScheme ≅
      (ambientHilbertSupportOpen R I' d K' (j ⁻¹ᵁ U)).toScheme :=
  openAmbientOverlapIso R I I' d K K' (i ⁻¹ᵁ U) (j ⁻¹ᵁ U)
    (commonAmbientOpenIso i j U hU hV)
    (commonAmbientOpenIso_coefficient R I I' K K' z i j hi hj U hU hV)

/-- The common-open Hilbert comparison preserves its actual base structure. -/
theorem commonAmbientHilbertIso_over :
    (commonAmbientHilbertIso R I I' d K K' z i j hi hj U hU hV).hom ≫
        openAmbientHilbertStructure R I' d K' (j ⁻¹ᵁ U) =
      openAmbientHilbertStructure R I d K (i ⁻¹ᵁ U) := openAmbientOverlapIso_over ..

/-- Every common triple open satisfies the actual Hilbert scheme cocycle. -/
theorem commonAmbientHilbertIso_trans (hW : U ≤ k.opensRange) :
    commonAmbientHilbertIso R I I' d K K' z i j hi hj U hU hV ≪≫
        commonAmbientHilbertIso R I' I'' d K' K'' z j k hj hk U hV hW =
      commonAmbientHilbertIso R I I'' d K K'' z i k hi hk U hU hW := by
  unfold commonAmbientHilbertIso
  rw [openAmbientOverlapIso_trans]
  congr 1
  exact commonAmbientOpenIso_trans i j k U hU hV hW

/-- The full pairwise common chart open supplies the actual Hilbert overlap comparison. -/
def pairwiseAmbientHilbertIso :
    (ambientHilbertSupportOpen R I d K (i ⁻¹ᵁ (i.opensRange ⊓ j.opensRange))).toScheme ≅
      (ambientHilbertSupportOpen R I' d K'
        (j ⁻¹ᵁ (i.opensRange ⊓ j.opensRange))).toScheme :=
  commonAmbientHilbertIso R I I' d K K' z i j hi hj _ inf_le_left inf_le_right

end FLT.Mazur.HilbertChart
