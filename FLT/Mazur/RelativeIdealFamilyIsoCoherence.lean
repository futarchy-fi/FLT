/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeIdealFamilyIsomorphism

/-!
# Coherence of intrinsic full-family transport

Identity and composition of actual ambient isomorphisms induce identity and
composition on the actual base-changed ambients and their complete ideals.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace FLT.Mazur.ClosedIdealCover

variable {A B C S X : Scheme.{u}} (a : A ⟶ S) (b : B ⟶ S) (c : C ⟶ S)
variable (e : A ≅ B) (f : B ≅ C) (he : e.hom ≫ b = a) (hf : f.hom ≫ c = b)
variable (s : X ⟶ S) (d : ℕ)

/-- Identity ambient transport is the identity on the actual scheme pullback. -/
theorem relativeIdealAmbientIso_refl :
    relativeIdealAmbientIso (Iso.refl A) a a (Category.id_comp a) s = Iso.refl _ := by
  apply Iso.ext
  apply pullback.hom_ext <;>
    simp only [relativeIdealAmbientIso_hom_fst, relativeIdealAmbientIso_hom_snd,
      Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- Ambient transport respects composition as actual scheme isomorphisms. -/
theorem relativeIdealAmbientIso_trans :
    relativeIdealAmbientIso (e ≪≫ f) a c
        ((Category.assoc _ _ _).trans ((congrArg (e.hom ≫ ·) hf).trans he)) s =
      relativeIdealAmbientIso e a b he s ≪≫ relativeIdealAmbientIso f b c hf s := by
  apply Iso.ext
  apply pullback.hom_ext <;>
    simp only [Iso.trans_hom, Category.assoc, relativeIdealAmbientIso_hom_fst,
      relativeIdealAmbientIso_hom_snd, relativeIdealAmbientIso_hom_snd_assoc]

/-- Identity transport fixes the entire intrinsic ideal family. -/
theorem relativeIdealFamilyIsoEquiv_refl (J : RelativeIdealFamilies a d s) :
    relativeIdealFamilyIsoEquiv (Iso.refl A) a a (Category.id_comp a) s d J = J := by
  apply Subtype.ext
  change J.val.comap (relativeIdealAmbientIso _ _ _ _ _).inv = J.val
  rw [relativeIdealAmbientIso_refl]
  exact comap_id J.val

/-- Successive ambient isomorphisms satisfy the cocycle on complete intrinsic family ideals. -/
theorem relativeIdealFamilyIsoEquiv_trans (J : RelativeIdealFamilies a d s) :
    relativeIdealFamilyIsoEquiv f b c hf s d (relativeIdealFamilyIsoEquiv e a b he s d J) =
      relativeIdealFamilyIsoEquiv (e ≪≫ f) a c
        ((Category.assoc _ _ _).trans ((congrArg (e.hom ≫ ·) hf).trans he)) s d J := by
  apply Subtype.ext
  change (J.val.comap (relativeIdealAmbientIso e a b he s).inv).comap
      (relativeIdealAmbientIso f b c hf s).inv =
    J.val.comap (relativeIdealAmbientIso (e ≪≫ f) a c _ s).inv
  rw [relativeIdealAmbientIso_trans, Iso.trans_inv, comap_comp]

end FLT.Mazur.ClosedIdealCover
