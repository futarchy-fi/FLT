/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineChartSectionLineRecovery

/-!
# Normalized line charts of an actual affine projective point

Every projective morphism is locally the point of an actual normalized
section submodule. The affine neighborhoods and coordinate charts are
constructed from the original morphism, with its coefficient map preserved.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] {ι : Type u}
variable {X : Scheme.{u}} [IsAffine X] (φ : R →+* Γ(X, ⊤))
variable (p : X ⟶ space R ι)
variable (hp : p ≫ baseProjection R ι = X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ))

include hp in
/-- Every point has an affine neighborhood where the actual morphism is a section-line point. -/
lemma exists_local_sectionLine (x : X) :
    ∃ (U : X.Opens) (hU : IsAffine U.toScheme), x ∈ U ∧
      let _ := hU
      ∃ (i : ι)
      (L : NormalizedSectionLine.Chart Γ(U.toScheme, ⊤) ι i),
      U.ι ≫ p = affineSectionLinePoint (U.ι.appTop.hom.comp φ) i L := by
  obtain ⟨i, hi⟩ := exists_mem_chart R ι (p x)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ p ⁻¹ᵁ chart R ι i from hi) (p ⁻¹ᵁ chart R ι i).isOpen
  change X.Opens at U
  let _ : IsAffine U.toScheme := hU
  have h : U ≤ p ⁻¹ᵁ chart R ι i := hUV
  let q := X.homOfLE h ≫ (p ∣_ chart R ι i) ≫ (chartIso R ι i).hom
  have hq : q ≫ chartMap R ι i = U.ι ≫ p := by
    dsimp only [q, chartMap]
    rw [Category.assoc, Category.assoc, Iso.hom_inv_id_assoc,
      morphismRestrict_ι, ← Category.assoc, X.homOfLE_ι]
  have hb : q ≫ Spec.map (CommRingCat.ofHom (chartScalars R ι i)) =
      U.toScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (U.ι.appTop.hom.comp φ)) := by
    have hc : chartMap R ι i ≫ baseProjection R ι =
        Spec.map (CommRingCat.ofHom (chartScalars R ι i)) := chartMap_baseProjection R ι i
    rw [← hc, ← Category.assoc, hq, Category.assoc, hp,
      ← Category.assoc, ← Scheme.isoSpec_hom_naturality, Category.assoc, ← Spec.map_comp]
    rfl
  exact ⟨U, hU, hxU, i, affineChartSectionLine _ i q hb,
    hq.symm.trans (affineChartSectionLine_point _ i q hb).symm⟩

end FLT.Mazur.ProjectiveSpace
