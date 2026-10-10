/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSectionPullbackCoordinates
public import FLT.Mazur.FiberwiseRegularFlatQuotient

/-!
# Residue tensor equations from affine section frames

On an actual spectrum, the scalar of a pulled section is the image of its
original coefficient under the ring map. Monicity on the residue tensor
spectra therefore supplies the fiberwise regularity criterion for the full
principal quotient, rather than a quotient by the radical.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.AffineSectionResidueEquation
open FCurve LineSectionPullbackCoordinates
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R B C : Type} [CommRing R] [CommRing B] [CommRing C]
  {L : (Spec (CommRingCat.of B)).Modules}

/-- The coefficient of the section in an actual sheaf frame on a spectrum. -/
def coefficient (e : L ≅ structureModule _) (s : Γ(L, ⊤)) : B :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).hom (e.hom.app ⊤ s)

/-- The spectrum section comparison identifies the pulled scalar with the ring-map image. -/
lemma coefficient_map (φ : B →+* C) (e : L ≅ structureModule _) (s : Γ(L, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of C)).hom
      ((Spec.map (CommRingCat.ofHom φ)).appTop (e.hom.app ⊤ s)) =
        φ (coefficient e s) := by
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom φ)) _

/-- Monicity after spectrum pullback gives regularity of the actual coefficient image. -/
theorem regular_image (φ : B →+* C) (e : L ≅ structureModule _) (s : Γ(L, ⊤))
    [Mono (globalSectionHom _ (pullGlobal (Spec.map (CommRingCat.ofHom φ)) L s))] :
    IsRegular (φ (coefficient e s)) := by
  have hr := regular_pulled_coordinate (Spec.map (CommRingCat.ofHom φ)) e s
  let c := (Scheme.ΓSpecIso (CommRingCat.of C)).commRingCatIsoToRingEquiv
  rw [← coefficient_map φ e s, ← isLeftRegular_iff_isRegular]
  intro a b hab
  change c ((Spec.map (CommRingCat.ofHom φ)).appTop (e.hom.app ⊤ s)) * a =
    c ((Spec.map (CommRingCat.ofHom φ)).appTop (e.hom.app ⊤ s)) * b at hab
  apply c.symm.injective
  apply hr.left
  simpa only [map_mul, RingEquiv.symm_apply_apply] using congrArg c.symm hab

variable [Algebra R B] [IsNoetherianRing R] [IsNoetherianRing B] [Module.Flat R B]

/-- Monic residue pullbacks construct regularity and flatness of the full affine quotient. -/
theorem regular_and_flat (e : L ≅ structureModule _) (s : Γ(L, ⊤))
    (hs : ∀ (p : Ideal R) [p.IsPrime], Mono (globalSectionHom _
      (pullGlobal (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[R] p.ResidueField ⊗[R] B).toRingHom)) L s))) :
    IsRegular (coefficient e s) ∧ Module.Flat R (B ⧸ Ideal.span {coefficient e s}) := by
  apply FiberwiseRegularFlatQuotient.regular_and_flat
  intro p _
  let _ := hs p
  exact regular_image
    (Algebra.TensorProduct.includeRight : B →ₐ[R] p.ResidueField ⊗[R] B).toRingHom e s

end FLT.Mazur.AffineSectionResidueEquation
