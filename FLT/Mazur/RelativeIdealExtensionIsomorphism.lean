/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeIdealOpenExtension
public import FLT.Mazur.IdealIsomorphismExtension

/-!
# Full relative extension is invariant under original ambient comparisons

Isomorphic original opens in a shared separated ambient extend transported
full families to the same full ideal. This is the compatibility used when
comparing universal chart ideals on Hilbert overlaps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.IdealSheafData FLT.Mazur.OpenIdealCover

universe u

namespace FLT.Mazur.ClosedIdealCover

set_option backward.isDefEq.respectTransparency false

variable {A B Z S X : Scheme.{u}} (a : A ⟶ S) (b : B ⟶ S) (z : Z ⟶ S)
variable (e : A ≅ B) (he : e.hom ≫ b = a)
variable (i : A ⟶ Z) (j : B ⟶ Z) [IsOpenImmersion i] [IsOpenImmersion j]
variable (hi : i ≫ z = a) (hj : j ≫ z = b) (h : e.hom ≫ j = i)
variable [IsSeparated z] (s : X ⟶ S) (d : ℕ)

include h in
/-- Transport across original ambient comparisons does not change the extended full family. -/
theorem relativeIdealFamilyExtension_iso (J : RelativeIdealFamilies a d s) :
    relativeIdealFamilyExtension b z j hj s d (relativeIdealFamilyIsoEquiv e a b he s d J) =
      relativeIdealFamilyExtension a z i hi s d J := by
  apply Subtype.ext
  change (J.val.comap (relativeIdealAmbientIso e a b he s).inv).map
      (relativeIdealAmbientHom b z j hj s) = J.val.map (relativeIdealAmbientHom a z i hi s)
  rw [← idealIso_map_eq_comap, ← map_comp]
  congr 1
  apply pullback.hom_ext
  · simp only [Category.assoc, relativeIdealAmbientHom_fst, relativeIdealAmbientIso_hom_fst]
  · simp only [Category.assoc, relativeIdealAmbientHom_snd,
      relativeIdealAmbientIso_hom_snd_assoc]
    rw [h]

end FLT.Mazur.ClosedIdealCover
