/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenImmersionIdealCorrespondence

/-!
# Full ideal extension commutes with ambient isomorphisms

Transport by inverse pullback equals direct image by the isomorphism. Hence
extension of complete ideals commutes with every commuting ambient square.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace FLT.Mazur.OpenIdealCover

variable {A B A' B' : Scheme.{u}} (e : A ≅ B)

/-- Direct image under an isomorphism is full-ideal pullback under its inverse. -/
theorem idealIso_map_eq_comap (J : A.IdealSheafData) : J.map e.hom = J.comap e.inv := by
  have h := open_map_comap e.inv J (by
    intro x _
    exact ⟨e.hom x, congrArg (fun f : A ⟶ A ↦ f x) e.hom_inv_id⟩)
  have h' := congrArg (fun L : A.IdealSheafData ↦ L.map e.hom) h
  rw [← map_comp, e.inv_hom_id, map_id] at h'
  exact h'.symm

/-- Commuting ambient squares preserve extension of entire ideal sheaves under transport. -/
theorem idealIso_extension (e' : A' ≅ B') (i : A ⟶ A') (j : B ⟶ B')
    (h : e.hom ≫ j = i ≫ e'.hom) (J : A.IdealSheafData) :
    (J.comap e.inv).map j = (J.map i).comap e'.inv := by
  rw [← idealIso_map_eq_comap, ← idealIso_map_eq_comap, ← map_comp, h, map_comp]

end FLT.Mazur.OpenIdealCover
