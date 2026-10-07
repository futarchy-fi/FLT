/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafOpenIsoDetection
public import FLT.Mazur.IdealModulePullbackRestrict

/-!
# Detecting module isomorphisms through open-immersion pullbacks

A jointly surjective family of open immersions detects whether a module
morphism is invertible. The criterion uses actual geometric pullbacks,
so affine charts need not first be replaced by their image opens.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u v

namespace FLT.Mazur.ModuleSheafPullbackIsoDetection

variable {X : Scheme.{u}} {M N : X.Modules}

/-- Pullback invertibility along an open immersion implies invertibility on its image. -/
lemma isIso_restrict_opensRange (a : M ⟶ N) {Y : Scheme.{u}}
    (i : Y ⟶ X) [IsOpenImmersion i] [IsIso ((pullback i).map a)] :
    IsIso ((restrictFunctor i.opensRange.ι).map a) := by
  have : IsIso ((restrictFunctor i).map a) :=
    (NatIso.isIso_map_iff (restrictFunctorIsoPullback i) a).mpr inferInstance
  exact FCurve.moduleHom_isIso_restrict_opensRange a i

/-- Jointly surjective open immersions detect isomorphisms through actual sheaf pullbacks. -/
lemma isIso_of_openImmersionPullbacks (a : M ⟶ N) {ι : Type v}
    (Y : ι → Scheme.{u}) (i : ∀ j, Y j ⟶ X) [∀ j, IsOpenImmersion (i j)]
    (hcover : ∀ x : X, ∃ j, x ∈ Set.range (i j))
    (ha : ∀ j, IsIso ((pullback (i j)).map a)) : IsIso a := by
  apply FCurve.ModuleSheafOpenIsoDetection.isIso_of_openCover a
    (fun j ↦ (i j).opensRange) hcover
  intro j
  let _ := ha j
  exact isIso_restrict_opensRange a (i j)

end FLT.Mazur.ModuleSheafPullbackIsoDetection
