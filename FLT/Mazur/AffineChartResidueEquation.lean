/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSectionResidueEquation
public import FLT.Mazur.OpenSectionMonicity

/-!
# Residue equations on arbitrary affine source charts

The canonical spectrum isomorphism normalizes the actual frame scalar to
itself. Monicity on the residue tensor charts therefore gives regularity
and a flat quotient over the original coefficient ring on any affine scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.AffineChartResidueEquation
open FCurve LineSectionPullbackCoordinates
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X : Scheme.{0}} [IsAffine X] {L : X.Modules}

/-- The actual affine chart morphism induced by a map on global functions. -/
def chartMap {C : Type} [CommRing C] (φ : Γ(X, ⊤) →+* C) :
    Spec (CommRingCat.of C) ⟶ X :=
  Spec.map (CommRingCat.ofHom φ) ≫ X.isoSpec.inv

/-- Passage to the canonical spectrum leaves the actual affine frame scalar unchanged. -/
lemma coefficient_isoSpec (e : L ≅ structureModule X) (s : Γ(L, ⊤)) :
    AffineSectionResidueEquation.coefficient (frame X.isoSpec.inv e)
      (pullGlobal X.isoSpec.inv L s) = e.hom.app ⊤ s := by
  unfold AffineSectionResidueEquation.coefficient
  rw [frame_section]
  have h : X.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(X, ⊤)).hom = 𝟙 _ := by
    rw [← Scheme.toSpecΓ_appTop]
    change X.isoSpec.inv.appTop ≫ X.isoSpec.hom.appTop = _
    rw [← Scheme.Hom.comp_appTop, X.isoSpec.hom_inv_id, Scheme.Hom.id_appTop]
  exact ConcreteCategory.congr_hom h _

variable {R : Type} [CommRing R] [Algebra R Γ(X, ⊤)]
  [IsNoetherianRing R] [IsNoetherianRing Γ(X, ⊤)] [Module.Flat R Γ(X, ⊤)]

/-- Monic residue tensor charts construct regularity and the full flat affine quotient. -/
theorem regular_and_flat (e : L ≅ structureModule X) (s : Γ(L, ⊤))
    (hs : ∀ (p : Ideal R) [p.IsPrime], Mono (globalSectionHom _
      (pullGlobal (chartMap (X := X) (Algebra.TensorProduct.includeRight :
        Γ(X, ⊤) →ₐ[R] p.ResidueField ⊗[R] Γ(X, ⊤)).toRingHom) L s))) :
    IsRegular (show Γ(X, ⊤) from e.hom.app ⊤ s) ∧
      Module.Flat R (Γ(X, ⊤) ⧸ Ideal.span {show Γ(X, ⊤) from e.hom.app ⊤ s}) := by
  have h := AffineSectionResidueEquation.regular_and_flat (R := R)
    (frame X.isoSpec.inv e) (pullGlobal X.isoSpec.inv L s) (fun p _ ↦
      (OpenSectionMonicity.comp_iff _ X.isoSpec.inv L s).mp (hs p))
  rwa [coefficient_isoSpec] at h

end FLT.Mazur.AffineChartResidueEquation
