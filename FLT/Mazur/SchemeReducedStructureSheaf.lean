/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeReducedRelativeSections

/-!
# Relative structure-sheaf comparison for a reduced pointed family

Apply the proved global comparison on each restricted family. The resulting
isomorphism is the actual map from the base structure sheaf to its direct image,
with no assumptions about the desired relative cohomology map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Opposite
namespace FLT.Mazur.SchemeReducedRelativeSections
variable {X S : Scheme.{0}} (f : X ⟶ S) (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
/-- Restrict the section using the actual open-base-change square. -/
def restrictedSection (U : S.Opens) : U.toScheme ⟶ (f ⁻¹ᵁ U).toScheme :=
  (isPullback_morphismRestrict f U).lift (𝟙 _) (U.ι ≫ s)
    (by simp only [Category.id_comp, Category.assoc, hs, Category.comp_id])
/-- The restricted section splits the restricted family map. -/
lemma restrictedSection_projection (U : S.Opens) :
    restrictedSection f s hs U ≫ f ∣_ U = 𝟙 _ :=
  (isPullback_morphismRestrict f U).lift_fst _ _ _
variable [IsProper f] [GeometricallyConnected f] [GeometricallyReduced f] [IsReduced X]
include s hs in
/-- Pullback of functions on every base open is an isomorphism. -/
lemma app_isIso (U : S.Opens) : IsIso (f.app U) := by
  have : IsIso (f ∣_ U).appTop :=
    (sectionsIso (f ∣_ U) (restrictedSection f s hs U)
      (restrictedSection_projection f s hs U)).isIso_hom
  rw [morphismRestrict_appTop] at this
  change IsIso (f.app (U.ι ''ᵁ ⊤) ≫
    X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op) at this
  rw [isIso_comp_right_iff] at this
  convert this using 1 <;> rw [U.ι_image_top]
include s hs in
/-- The original structure-presheaf map is an isomorphism. -/
lemma presheafMap_isIso : IsIso f.toPshHom.c := by
  have (U : S.Opensᵒᵖ) : IsIso (f.toPshHom.c.app U) := app_isIso f s hs U.unop
  exact NatIso.isIso_of_isIso_app _
/-- The actual structure-presheaf comparison, bundled as an isomorphism. -/
def structurePresheafIso :
    S.presheaf ≅ (TopCat.Presheaf.pushforward _ f.base).obj X.presheaf := by
  let _ := presheafMap_isIso f s hs
  exact asIso f.toPshHom.c
/-- The base structure sheaf is the direct image of the family structure sheaf. -/
def structureSheafIso :
    S.sheaf ≅ (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf where
  hom := ⟨(structurePresheafIso f s hs).hom⟩
  inv := ⟨(structurePresheafIso f s hs).inv⟩
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    exact (structurePresheafIso f s hs).hom_inv_id
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    exact (structurePresheafIso f s hs).inv_hom_id
/-- The sheaf comparison has the original structural map as its underlying morphism. -/
lemma structureSheafIso_hom : (structureSheafIso f s hs).hom.hom = f.toPshHom.c := rfl

/-- On each open, the comparison is the original pullback of functions. -/
lemma structureSheafIso_hom_app (U : S.Opens) :
    (structureSheafIso f s hs).hom.hom.app (op U) = f.app U := rfl

end FLT.Mazur.SchemeReducedRelativeSections
