/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertIntrinsicInclusion
public import FLT.Mazur.HilbertOpenInclusionExtension
public import FLT.Mazur.IdealIsomorphismExtension

/-!
# Intrinsic full-ideal extension classified by Hilbert inclusion

The Hilbert inclusion classifies direct image of the complete intrinsic
ideal along the base change of the original ambient inclusion. This is the
covariant compatibility needed for comparison of overlaps under restriction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover FLT.Mazur.OpenIdealCover

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ) (K : Ideal (MvPolynomial I R))
variable (U V : (Spec (.of (MvPolynomial I R ⧸ K))).Opens) (h : U ≤ V)
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R))

/-- Hilbert inclusion classifies extension of the full intrinsic ideal along ambient inclusion. -/
theorem openIntrinsicParameterInclusion_extension
    (p : OpenAmbientSchemeParameters R I d K U s) :
    (openIntrinsicSchemeClassification R I d K U s p).val.map
        (relativeIdealAmbientHom (quotientOriginalOpenStructure R I K U)
          (quotientOriginalOpenStructure R I K V)
          ((Spec (.of (MvPolynomial I R ⧸ K))).homOfLE h)
          (quotientOriginalOpenInclusion_over R I K U V h) s) =
      (openIntrinsicSchemeClassification R I d K V s
        (openAmbientParameterInclusion R I d K U V h s p)).val := by
  change ((openAmbientSchemeClassification R I d K U s p).val.comap
      (quotientRelativeOpenIso R I K U s).inv).map _ =
    (openAmbientSchemeClassification R I d K V s
      (openAmbientParameterInclusion R I d K U V h s p)).val.comap
        (quotientRelativeOpenIso R I K V s).inv
  rw [idealIso_extension (quotientRelativeOpenIso R I K U s)
    (quotientRelativeOpenIso R I K V s) _ _ (quotientRelativeOpenIso_inclusion R I K U V h s),
    openAmbientParameterInclusion_extension]

end FLT.Mazur.HilbertChart
