/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertIntrinsicExtension
public import FLT.Mazur.HilbertOpenAmbientOverlap
public import FLT.Mazur.RelativeIdealAmbientIsoSquare

/-!
# Actual Hilbert overlaps commute with smaller ambient opens

A commuting square of actual ambient open inclusions and ambient
isomorphisms induces a commuting square of Hilbert representatives. The
proof uses extension of full intrinsic ideals and their classification.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover FLT.Mazur.OpenIdealCover

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I I' : Type u) [CommRing R] (d : ℕ)
variable (K : Ideal (MvPolynomial I R)) (K' : Ideal (MvPolynomial I' R))
variable (U V : (Spec (.of (MvPolynomial I R ⧸ K))).Opens)
variable (U' V' : (Spec (.of (MvPolynomial I' R ⧸ K'))).Opens)
variable (h : U ≤ V) (h' : U' ≤ V') (e : U.toScheme ≅ U'.toScheme)
variable (f : V.toScheme ≅ V'.toScheme)
variable (he : e.hom ≫ quotientOriginalOpenStructure R I' K' U' =
  quotientOriginalOpenStructure R I K U)
variable (hf : f.hom ≫ quotientOriginalOpenStructure R I' K' V' =
  quotientOriginalOpenStructure R I K V)
variable (hc : e.hom ≫ (Spec (.of (MvPolynomial I' R ⧸ K'))).homOfLE h' =
  (Spec (.of (MvPolynomial I R ⧸ K))).homOfLE h ≫ f.hom)

include hc in
/-- On every test scheme, restricting ambient overlaps commutes with full-family parameters. -/
theorem openAmbientOverlapParameters_inclusion {X : Scheme.{u}} (s : X ⟶ Spec (.of R))
    (p : OpenAmbientSchemeParameters R I d K U s) :
    openAmbientParameterInclusion R I' d K' U' V' h' s
        (openAmbientOverlapParameters R I I' d K K' U U' e he s p) =
      openAmbientOverlapParameters R I I' d K K' V V' f hf s
        (openAmbientParameterInclusion R I d K U V h s p) := by
  apply (openIntrinsicSchemeClassification R I' d K' V' s).injective
  apply Subtype.ext
  rw [← openIntrinsicParameterInclusion_extension,
    openAmbientOverlapParameters_family, openAmbientOverlapParameters_family]
  change ((openIntrinsicSchemeClassification R I d K U s p).val.comap
      (relativeIdealAmbientIso e _ _ he s).inv).map _ =
    (openIntrinsicSchemeClassification R I d K V s
      (openAmbientParameterInclusion R I d K U V h s p)).val.comap
        (relativeIdealAmbientIso f _ _ hf s).inv
  rw [← openIntrinsicParameterInclusion_extension]
  exact idealIso_extension _ _ _ _
    (relativeIdealAmbientIso_square _ _ _ _ e f _ _ he hf
      (quotientOriginalOpenInclusion_over R I K U V h)
      (quotientOriginalOpenInclusion_over R I' K' U' V' h') hc s) _

include hc in
/-- Actual overlap morphisms commute with further ambient restriction as scheme morphisms. -/
theorem openAmbientOverlapIso_inclusion :
    openAmbientHilbertInclusion R I d K U V h ≫
        (openAmbientOverlapIso R I I' d K K' V V' f hf).hom =
      (openAmbientOverlapIso R I I' d K K' U U' e he).hom ≫
        openAmbientHilbertInclusion R I' d K' U' V' h' := by
  have hp := congrArg Subtype.val (openAmbientOverlapParameters_inclusion R I I' d K K'
    U V U' V' h h' e f he hf hc (openAmbientHilbertStructure R I d K U)
      ⟨𝟙 _, Category.id_comp _⟩)
  simp only [openAmbientParameterInclusion, openAmbientOverlapIso_parameters,
    Category.id_comp] at hp
  exact hp.symm

end FLT.Mazur.HilbertChart
