/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# The original coefficient algebra as functions on its spectrum

For an affine base, an algebra over its global functions defines an actual
change of base. The canonical spectrum-section isomorphism is linear for
that morphism's pullback action and the original algebra action.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineBaseChangeCoefficients
set_option backward.isDefEq.respectTransparency false
variable (S : Scheme) [IsAffine S]
  (B : Type) [CommRing B] [Algebra Γ(S, ⊤) B]

/-- The geometric change of base associated with the original coefficient algebra. -/
def baseMap : Spec (.of B) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) B)) ≫ S.isoSpec.inv

/-- The inverse affine presentation pulls functions back by the canonical spectrum map. -/
lemma isoSpec_inv_appTop : S.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(S, ⊤)).inv := by
  apply (cancel_mono (Scheme.ΓSpecIso Γ(S, ⊤)).hom).mp
  rw [← Scheme.toSpecΓ_appTop S, ← Scheme.Hom.comp_appTop,
    Scheme.toSpecΓ_isoSpec_inv, Scheme.Hom.id_appTop, Scheme.toSpecΓ_appTop]
  exact (Scheme.ΓSpecIso Γ(S, ⊤)).inv_hom_id.symm

/-- Structural pullback is exactly the given algebra map followed by spectrum sections. -/
lemma baseMap_appTop : (baseMap S B).appTop =
    CommRingCat.ofHom (algebraMap Γ(S, ⊤) B) ≫ (Scheme.ΓSpecIso (.of B)).inv := by
  rw [baseMap, Scheme.Hom.comp_appTop, isoSpec_inv_appTop]
  exact (Scheme.ΓSpecIso_inv_naturality _).symm

/-- Functions on the coefficient spectrum retain the original base module structure. -/
def coefficientEquiv :
    (ModuleCat.restrictScalars (baseMap S B).appTop.hom).obj
      (ModuleCat.of Γ(Spec (.of B), ⊤) Γ(Spec (.of B), ⊤)) ≃ₗ[Γ(S, ⊤)] B :=
  LinearEquiv.ofBijective
    ({ toFun := (Scheme.ΓSpecIso (.of B)).hom
       map_add' := map_add _
       map_smul' := fun r x ↦ by
         change (Scheme.ΓSpecIso (.of B)).hom ((baseMap S B).appTop r *
           (show Γ(Spec (.of B), ⊤) from x)) = r • _
         rw [map_mul, baseMap_appTop]
         change (Scheme.ΓSpecIso (.of B)).hom
           ((Scheme.ΓSpecIso (.of B)).inv (algebraMap Γ(S, ⊤) B r)) * _ = _
         rw [← CommRingCat.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply]
         exact (Algebra.smul_def r _).symm } :
      (ModuleCat.restrictScalars (baseMap S B).appTop.hom).obj
        (ModuleCat.of Γ(Spec (.of B), ⊤) Γ(Spec (.of B), ⊤)) →ₗ[Γ(S, ⊤)] B)
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of B)).hom)

/-- The coefficient equivalence is the original spectrum-section isomorphism. -/
lemma coefficientEquiv_apply (x : Γ(Spec (.of B), ⊤)) :
    coefficientEquiv S B x = (Scheme.ΓSpecIso (.of B)).hom x := rfl

end FLT.Mazur.AffineBaseChangeCoefficients
