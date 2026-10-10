/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativePicardBaseChangeGeometry

/-!
# Relative Picard presheaves under change of the fixed base

The fiber-product comparison induces a natural isomorphism of the quotient
presheaves. Both directions pull back actual line-bundle representatives.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.SchemePicard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X S S' : Scheme.{u}} (f : X ⟶ S) (a : S' ⟶ S)

/-- The relative Picard group comparison at a test scheme over the new base. -/
def relativeBaseChangeValueIso (T : Over S') :
    (relativePresheaf f).obj (op ((Over.map a).obj T)) ≅
      (relativePresheaf (Limits.pullback.snd f a)).obj (op T) where
  hom := CommGrpCat.ofHom (relativeMap _ _ (relativeBaseChangeTotalIso f a T).hom
    (𝟙 T.left) (by simp [relativeBaseChangeTotalIso]))
  inv := CommGrpCat.ofHom (relativeMap _ _ (relativeBaseChangeTotalIso f a T).inv
    (𝟙 T.left) (by simp [relativeBaseChangeTotalIso]))
  hom_inv_id := by
    apply CommGrpCat.Hom.ext
    apply MonoidHom.ext
    intro x
    obtain ⟨x, rfl⟩ := relativeClass_surjective _ x
    change relativeClass _
      (pullback (relativeBaseChangeTotalIso f a T).inv
        (pullback (relativeBaseChangeTotalIso f a T).hom x)) = relativeClass _ x
    rw [← pullback_comp, Iso.inv_hom_id, pullback_id]
  inv_hom_id := by
    apply CommGrpCat.Hom.ext
    apply MonoidHom.ext
    intro x
    obtain ⟨x, rfl⟩ := relativeClass_surjective _ x
    change relativeClass _
      (pullback (relativeBaseChangeTotalIso f a T).hom
        (pullback (relativeBaseChangeTotalIso f a T).inv x)) = relativeClass _ x
    rw [← pullback_comp, Iso.hom_inv_id, pullback_id]

/-- Change of the fixed base is a natural isomorphism of relative quotient presheaves. -/
def relativePresheafBaseChange :
    (Over.map a).op ⋙ relativePresheaf f ≅ relativePresheaf (Limits.pullback.snd f a) :=
  NatIso.ofComponents (fun T ↦ relativeBaseChangeValueIso f a T.unop) (fun {T U} g ↦ by
    apply CommGrpCat.Hom.ext
    apply MonoidHom.ext
    intro x
    obtain ⟨x, rfl⟩ := relativeClass_surjective _ x
    change relativeClass _
      (pullback (relativeBaseChangeTotalIso f a U.unop).hom
        (pullback (relativeTotalMap f ((Over.map a).map g.unop)) x)) =
      relativeClass _
        (pullback (relativeTotalMap (Limits.pullback.snd f a) g.unop)
          (pullback (relativeBaseChangeTotalIso f a T.unop).hom x))
    rw [← pullback_comp, ← pullback_comp, relativeBaseChangeTotalIso_naturality])

/-- The comparison acts on representatives by the actual fiber-product isomorphism. -/
lemma relativePresheafBaseChange_class (T : Over S')
    (x : Pic (Limits.pullback f ((Over.map a).obj T).hom)) :
    (relativePresheafBaseChange f a).hom.app (op T)
        (relativeClass (Limits.pullback.snd f ((Over.map a).obj T).hom) x) =
      relativeClass (Limits.pullback.snd (Limits.pullback.snd f a) T.hom)
        (pullback (relativeBaseChangeTotalIso f a T).hom x) := rfl

end FLT.Mazur.SchemePicard
