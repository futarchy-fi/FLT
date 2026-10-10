/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertCommonAmbientOverlap
public import FLT.Mazur.HilbertOverlapRestriction

/-!
# Hilbert chart comparisons on nested common opens

The actual Hilbert comparisons constructed from shared ambient charts commute
with further restriction of the common open. These are equalities of scheme
morphisms, obtained from the corresponding full-ideal extension comparisons.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.OpenIdealCover

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I I' : Type u) [CommRing R] (d : ℕ)
variable (K : Ideal (MvPolynomial I R)) (K' : Ideal (MvPolynomial I' R))
variable {Z : Scheme.{u}} (z : Z ⟶ Spec (.of R))
variable (i : Spec (.of (MvPolynomial I R ⧸ K)) ⟶ Z)
variable (j : Spec (.of (MvPolynomial I' R ⧸ K')) ⟶ Z)
variable [IsOpenImmersion i] [IsOpenImmersion j]
variable (hi : i ≫ z = Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial I R ⧸ K))))
variable (hj : j ≫ z = Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial I' R ⧸ K'))))
variable (U : Z.Opens) (hU : U ≤ i.opensRange) (hV : U ≤ j.opensRange)

/-- Shared-ambient Hilbert comparisons commute with shrinking the actual common open. -/
theorem commonAmbientHilbertIso_restrict (T : Z.Opens) (hTU : T ≤ U) :
    openAmbientHilbertInclusion R I d K (i ⁻¹ᵁ T) (i ⁻¹ᵁ U) (i.preimage_mono hTU) ≫
        (commonAmbientHilbertIso R I I' d K K' z i j hi hj U hU hV).hom =
      (commonAmbientHilbertIso R I I' d K K' z i j hi hj T
        (hTU.trans hU) (hTU.trans hV)).hom ≫
          openAmbientHilbertInclusion R I' d K' (j ⁻¹ᵁ T) (j ⁻¹ᵁ U)
            (j.preimage_mono hTU) := by
  unfold commonAmbientHilbertIso
  apply openAmbientOverlapIso_inclusion
  exact (commonAmbientOpenIso_restrict i j U hU hV T hTU).symm

end FLT.Mazur.HilbertChart
