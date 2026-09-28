/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Affine ideals of pullbacks

Pullback of ideal sheaves agrees with extension along the actual section map.
The affine comparison follows from the pullback/pushforward adjunction and the
order equivalence between ideal sheaves and ideals of global sections.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- On affine schemes, pullback extends the ideal of global sections. -/
lemma ideal_comap_top [IsAffine X] [IsAffine Y] (I : X.IdealSheafData) (k : Y ⟶ X) :
    (I.comap k).ideal ⟨⊤, isAffineOpen_top Y⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top X⟩).map k.appTop.hom := by
  apply le_antisymm
  · let J := ofIdealTop ((I.ideal ⟨⊤, isAffineOpen_top X⟩).map k.appTop.hom)
    suffices h : I.comap k ≤ J by
      simpa [J] using h ⟨⊤, isAffineOpen_top Y⟩
    apply le_map_iff_comap_le.mp
    apply le_of_isAffine
    rw [ideal_map_of_isAffineHom]
    simpa [Scheme.Hom.appTop, J] using
      (Ideal.le_comap_map : I.ideal ⟨⊤, isAffineOpen_top X⟩ ≤
        ((I.ideal ⟨⊤, isAffineOpen_top X⟩).map k.appTop.hom).comap k.appTop.hom)
  · rw [Ideal.map_le_iff_le_comap]
    have h := I.le_map_comap k ⟨⊤, isAffineOpen_top X⟩
    rw [ideal_map_of_isAffineHom] at h
    simpa [Scheme.Hom.appTop] using h

set_option backward.isDefEq.respectTransparency false in
/-- Restriction to an affine open preserves its ideal under the section isomorphism. -/
lemma ideal_comap_ι_top (I : X.IdealSheafData) (U : X.affineOpens) :
    (I.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top U⟩ =
      (I.ideal U).map U.1.topIso.inv.hom := by
  rw [ideal_comap_of_isOpenImmersion]
  simp only [Opens.ι_appIso, Iso.refl_inv]
  exact (I.map_ideal' (V := U)
    (U := ⟨U.1.ι ''ᵁ ⊤, (isAffineOpen_top U).image_of_isOpenImmersion U.1.ι⟩)
    (eqToHom U.1.ι_image_top).op).symm

set_option backward.isDefEq.respectTransparency false in
/-- On affine opens, pullback extends the ideal along the specified section map. -/
theorem ideal_comap (I : X.IdealSheafData) (k : Y ⟶ X)
    (V : X.affineOpens) (U : Y.affineOpens) (e : U.1 ≤ k ⁻¹ᵁ V.1) :
    (I.comap k).ideal U = (I.ideal V).map (k.appLE V U e).hom := by
  have h := ideal_comap_top (I.comap V.1.ι) (k.resLE V U e)
  rw [← comap_comp, Scheme.Hom.resLE_comp_ι, comap_comp,
    ideal_comap_ι_top, ideal_comap_ι_top] at h
  apply_fun Ideal.map U.1.topIso.hom.hom at h
  simpa only [Ideal.map_map, ← CommRingCat.hom_comp, Scheme.Hom.appTop,
    Scheme.Hom.resLE_app_top, Category.assoc, Iso.inv_hom_id,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id,
    CommRingCat.hom_id, Ideal.map_id] using h

/-- A principal ideal pulls back to the image of its chosen generator. -/
theorem ideal_comap_of_span_singleton (I : X.IdealSheafData) (k : Y ⟶ X)
    (V : X.affineOpens) (U : Y.affineOpens) (e : U.1 ≤ k ⁻¹ᵁ V.1)
    (a : Γ(X, V)) (ha : I.ideal V = Ideal.span {a}) :
    (I.comap k).ideal U = Ideal.span {(k.appLE V U e).hom a} := by
  rw [ideal_comap I k V U e, ha, Ideal.map_span, Set.image_singleton]

end AlgebraicGeometry.Scheme.IdealSheafData
