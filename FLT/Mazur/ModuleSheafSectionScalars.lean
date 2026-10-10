/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Scalars under reindexing and direct image of module sections

These formulas retain the geometric structure-sheaf action while sections
are transported along equal opens or projected to a chart pushforward.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.ModuleSheafSectionScalars

/-- Transport between equal opens is semilinear for the same structure restriction. -/
lemma reindex_smul {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (h : U = V)
    (r : Γ(X, U)) (s : Γ(M, U)) :
    (M.presheaf.mapIso (eqToIso h.symm).op).hom (r • s) =
      X.presheaf.map (eqToHom h.symm).op r •
        (M.presheaf.mapIso (eqToIso h.symm).op).hom s := by
  subst V
  simp

/-- The pushforward action is precisely pullback of structure sections. -/
lemma pushforward_smul {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules)
    (U : Y.Opens) (r : Γ(Y, U)) (s : Γ((pushforward f).obj M, U)) :
    r • s = f.app U r • (show Γ(M, f ⁻¹ᵁ U) from s) := rfl

/-- A module map into a chart pushforward preserves the geometric scalar action. -/
lemma projection_smul {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules)
    {N : Y.Modules} (p : N ⟶ (pushforward f).obj M)
    (U : Y.Opens) (r : Γ(Y, U)) (s : Γ(N, U)) :
    p.app U (r • s) = f.app U r • (show Γ(M, f ⁻¹ᵁ U) from p.app U s) :=
  p.app_smul r s

/-- Reindexing a direct image to a specified preimage keeps the original scalar map. -/
lemma pushforward_reindex_smul {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules)
    (U : Y.Opens) (V : X.Opens) (h : f ⁻¹ᵁ U = V)
    (r : Γ(Y, U)) (s : Γ((pushforward f).obj M, U)) :
    (M.presheaf.mapIso (eqToIso h.symm).op).hom (r • s) =
      f.appLE U V h.ge r • (M.presheaf.mapIso (eqToIso h.symm).op).hom s := by
  exact reindex_smul M h (f.app U r) s

end FLT.Mazur.ModuleSheafSectionScalars
