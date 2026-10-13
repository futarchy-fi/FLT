/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationInvariantSpectrum

/-!
# The invariant spectrum is universal for invariant maps to affine schemes

Every full-invariant morphism to an affine target factors uniquely through
the constructed invariant spectrum. This is an affine-target universal
property; scheme effectivity and the full kernel pair remain separate claims.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationInvariantSpectrum
open SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
variable {D A : Scheme.{u}} (p q : D ⟶ A)

/-- A full-invariant scheme map pulls back every regular function into the actual invariant ring. -/
def invariantPullback {Y : Scheme.{u}} (g : A ⟶ Y) (hg : p ≫ g = q ≫ g) :
    Γ(Y, ⊤) ⟶ CommRingCat.of (compatibleFunctions p q) :=
  CommRingCat.ofHom (g.appTop.hom.codRestrict (compatibleFunctions p q) fun s ↦
    show p.appTop (g.appTop s) = q.appTop (g.appTop s) from
      congrArg (fun h : D ⟶ Y ↦ h.appTop s) hg)

/-- Forgetting the invariant subtype recovers the unchanged original coefficient map. -/
@[reassoc]
theorem invariantPullback_inclusion {Y : Scheme.{u}} (g : A ⟶ Y)
    (hg : p ≫ g = q ≫ g) : invariantPullback p q g hg ≫ inclusion p q = g.appTop := rfl

/-- The actual factorization into an affine target. -/
def descend {Y : Scheme.{u}} [IsAffine Y] (g : A ⟶ Y) (hg : p ≫ g = q ≫ g) :
    target p q ⟶ Y := Spec.map (invariantPullback p q g hg) ≫ Y.isoSpec.inv

/-- The constructed factorization retains the original morphism and all of its sheaf maps. -/
@[reassoc]
theorem projection_descend {Y : Scheme.{u}} [IsAffine Y] (g : A ⟶ Y)
    (hg : p ≫ g = q ≫ g) : projection p q ≫ descend p q g hg = g := by
  unfold projection descend
  rw [Category.assoc, ← Category.assoc (Spec.map _), ← Spec.map_comp,
    invariantPullback_inclusion, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
    Category.assoc, ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id]

/-- The source pullback from the invariant spectrum is injective on actual regular functions. -/
theorem projection_appTop_injective : Function.Injective (projection p q).appTop := by
  have h : (projection p q).appTop =
      (Scheme.ΓSpecIso (.of (compatibleFunctions p q))).hom ≫ inclusion p q := by
    rw [← Iso.inv_comp_eq]
    exact projection_coefficients p q
  rw [h]
  exact Subtype.val_injective.comp
    (Scheme.ΓSpecIso (.of (compatibleFunctions p q))).commRingCatIsoToRingEquiv.injective

/-- Morphisms from this spectrum to an affine target are detected on the original source. -/
theorem affine_hom_ext {Y : Scheme.{u}} [IsAffine Y] {g h : target p q ⟶ Y}
    (he : projection p q ≫ g = projection p q ≫ h) : g = h := by
  have hc : g.appTop = h.appTop := by
    ext s
    apply projection_appTop_injective p q
    exact congrArg (fun a ↦ a.appTop s) he
  apply (cancel_mono Y.isoSpec.hom).mp
  rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality, hc]

/-- The constructed invariant affine model has the exact universal property for affine tests. -/
theorem existsUnique_affine_factor {Y : Scheme.{u}} [IsAffine Y] (g : A ⟶ Y)
    (hg : p ≫ g = q ≫ g) : ∃! h : target p q ⟶ Y, projection p q ≫ h = g :=
  ⟨descend p q g hg, projection_descend p q g hg,
    fun _ he ↦ affine_hom_ext p q (he.trans (projection_descend p q g hg).symm)⟩

end FLT.Mazur.SchemeRelationInvariantSpectrum
