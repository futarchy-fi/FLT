/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOpenAmbientOverlap
public import FLT.Mazur.RelativeIdealFamilyIsoCoherence

/-!
# Scheme-level coherence of Hilbert overlap isomorphisms

The actual Hilbert comparisons preserve identity and composition of original
ambient isomorphisms. The proof uses classification of complete intrinsic
ideals on every test scheme and evaluates it on the identity parameter.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover FLT.Mazur.OpenIdealCover

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I I' I'' : Type u) [CommRing R] (d : ℕ)
variable (K : Ideal (MvPolynomial I R)) (K' : Ideal (MvPolynomial I' R))
variable (K'' : Ideal (MvPolynomial I'' R))
variable (U : (Spec (.of (MvPolynomial I R ⧸ K))).Opens)
variable (V : (Spec (.of (MvPolynomial I' R ⧸ K'))).Opens)
variable (W : (Spec (.of (MvPolynomial I'' R ⧸ K''))).Opens)
variable (e : U.toScheme ≅ V.toScheme) (f : V.toScheme ≅ W.toScheme)
variable (he : e.hom ≫ quotientOriginalOpenStructure R I' K' V =
  quotientOriginalOpenStructure R I K U)
variable (hf : f.hom ≫ quotientOriginalOpenStructure R I'' K'' W =
  quotientOriginalOpenStructure R I' K' V)

/-- Identity ambient comparison fixes every Hilbert parameter of the open. -/
theorem openAmbientOverlapParameters_refl {X : Scheme.{u}} (s : X ⟶ Spec (.of R))
    (p : OpenAmbientSchemeParameters R I d K U s) :
    openAmbientOverlapParameters R I I d K K U U (Iso.refl _) (Category.id_comp _) s p = p := by
  apply (openIntrinsicSchemeClassification R I d K U s).injective
  rw [openAmbientOverlapParameters_family, relativeIdealFamilyIsoEquiv_refl]

/-- Composition of ambient comparisons gives composition on every full-family parameter. -/
theorem openAmbientOverlapParameters_trans {X : Scheme.{u}} (s : X ⟶ Spec (.of R))
    (p : OpenAmbientSchemeParameters R I d K U s) :
    openAmbientOverlapParameters R I' I'' d K' K'' V W f hf s
        (openAmbientOverlapParameters R I I' d K K' U V e he s p) =
      openAmbientOverlapParameters R I I'' d K K'' U W (e ≪≫ f)
        ((Category.assoc _ _ _).trans ((congrArg (e.hom ≫ ·) hf).trans he)) s p := by
  apply (openIntrinsicSchemeClassification R I'' d K'' W s).injective
  rw [openAmbientOverlapParameters_family, openAmbientOverlapParameters_family,
    openAmbientOverlapParameters_family, relativeIdealFamilyIsoEquiv_trans]

/-- The actual Hilbert overlap isomorphism for the identity ambient is the identity. -/
theorem openAmbientOverlapIso_refl :
    openAmbientOverlapIso R I I d K K U U (Iso.refl _) (Category.id_comp _) = Iso.refl _ := by
  apply Iso.ext
  have h := congrArg Subtype.val (openAmbientOverlapParameters_refl R I d K U
    (openAmbientHilbertStructure R I d K U) ⟨𝟙 _, Category.id_comp _⟩)
  rw [openAmbientOverlapIso_parameters, Category.id_comp] at h
  exact h

/-- Actual Hilbert overlap isomorphisms satisfy composition, hence the ambient cocycle. -/
theorem openAmbientOverlapIso_trans :
    openAmbientOverlapIso R I I' d K K' U V e he ≪≫
        openAmbientOverlapIso R I' I'' d K' K'' V W f hf =
      openAmbientOverlapIso R I I'' d K K'' U W (e ≪≫ f)
        ((Category.assoc _ _ _).trans ((congrArg (e.hom ≫ ·) hf).trans he)) := by
  apply Iso.ext
  have h := congrArg Subtype.val (openAmbientOverlapParameters_trans R I I' I'' d K K' K''
    U V W e f he hf (openAmbientHilbertStructure R I d K U) ⟨𝟙 _, Category.id_comp _⟩)
  rw [openAmbientOverlapIso_parameters, openAmbientOverlapIso_parameters,
    openAmbientOverlapIso_parameters, Category.id_comp, Category.id_comp] at h
  exact h

end FLT.Mazur.HilbertChart
