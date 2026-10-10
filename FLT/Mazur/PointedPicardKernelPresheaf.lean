/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointedPicardBaseChange

/-!
# The normalized Picard kernel presheaf

The kernel of restriction at the chosen section is naturally isomorphic to
the relative Picard quotient presheaf, before any sheafification.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.SchemePicard
variable {X S : Scheme.{u}} (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)

/-- Classes trivial at the section, with actual Picard pullback as restriction. -/
def pointedKernelPresheaf : (Over S)ᵒᵖ ⥤ CommGrpCat where
  obj T := CommGrpCat.of (pullback (pointedBaseSection f e he T.unop)).ker
  map g := CommGrpCat.ofHom (pointedKernelMap f e he g.unop)
  map_id T := by
    apply CommGrpCat.Hom.ext
    apply MonoidHom.ext
    intro a
    apply Subtype.ext
    change pullback (relativeTotalMap f (𝟙 T.unop)) a.val = a.val
    rw [relativeTotalMap_id, pullback_id]
  map_comp {T U V} g h := by
    apply CommGrpCat.Hom.ext
    apply MonoidHom.ext
    intro a
    apply Subtype.ext
    change pullback (relativeTotalMap f (g ≫ h).unop) a.val =
      pullback (relativeTotalMap f h.unop) (pullback (relativeTotalMap f g.unop) a.val)
    rw [unop_comp, relativeTotalMap_comp, pullback_comp]

/-- The pointwise quotient-to-kernel equivalence using the original base section. -/
def pointedKernelValueIso (T : Over S) :
    (relativePresheaf f).obj (op T) ≅ (pointedKernelPresheaf f e he).obj (op T) :=
  (relativeKernelEquiv (Limits.pullback.snd f T.hom) (pointedBaseSection f e he T)
    (pointedBaseSection_snd f e he T)).toCommGrpIso

/-- The pointwise equivalence computes normalization on the original representative. -/
@[simp]
theorem pointedKernelValueIso_class (T : Over S) (a : Pic (Limits.pullback f T.hom)) :
    ((pointedKernelValueIso f e he T).hom
      (relativeClass (Limits.pullback.snd f T.hom) a)).val =
        normalize (Limits.pullback.snd f T.hom) (pointedBaseSection f e he T) a := rfl

/-- Normalization identifies the quotient and kernel as presheaves, not only pointwise. -/
def relativePointedKernelIso : relativePresheaf f ≅ pointedKernelPresheaf f e he :=
  NatIso.ofComponents (fun T ↦ pointedKernelValueIso f e he T.unop) (fun {T U} g ↦ by
    apply CommGrpCat.Hom.ext
    apply MonoidHom.ext
    intro a
    obtain ⟨a, rfl⟩ := relativeClass_surjective _ a
    apply Subtype.ext
    exact normalize_baseMap f e he g.unop a)

/-- The inverse comparison simply takes the relative class of the normalized bundle. -/
@[simp]
theorem relativePointedKernelIso_inv (T : Over S)
    (a : (pullback (pointedBaseSection f e he T)).ker) :
    (relativePointedKernelIso f e he).inv.app (op T) a =
      relativeClass (Limits.pullback.snd f T.hom) a.val := rfl

end FLT.Mazur.SchemePicard
