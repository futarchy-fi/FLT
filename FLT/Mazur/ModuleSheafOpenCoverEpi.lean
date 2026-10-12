/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafOpenImmersionLocalHom

/-!
# Detecting epimorphisms on an open scheme cover

The original open pullbacks detect epimorphisms because equality of sheaf
morphisms is local on the source scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.ModuleSheafOpenImmersionLocalHom
variable {X : Scheme.{u}} {J : Type u} (Y : J → Scheme.{u})
  (i : ∀ j, Y j ⟶ X) [∀ j, IsOpenImmersion (i j)]
variable (hcover : iSup (fun j ↦ (i j).opensRange) = ⊤)
variable {M N : X.Modules} (q : M ⟶ N)

include hcover in
/-- A map whose pullbacks are epi on an open cover is globally epi. -/
theorem epi_of_openCover [∀ j, Epi ((pullback (i j)).map q)] : Epi q := by
  constructor
  intro P a b hab
  apply ModuleSheafMorphismGluing.hom_ext (fun j ↦ (i j).opensRange) hcover
  intro j
  rw [← localHom_map (i j) a, ← localHom_map (i j) b]
  congr 1
  apply (cancel_epi ((pullback (i j)).map q)).mp
  simpa only [Functor.map_comp] using congrArg ((pullback (i j)).map) hab

end FLT.Mazur.ModuleSheafOpenImmersionLocalHom
