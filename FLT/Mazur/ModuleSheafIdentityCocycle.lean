/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafIdentityRecovery

/-!
# Identity normalization with a fixed comparison isomorphism

A separately identified composition isomorphism suffices to normalize a
self-transition, keeping concrete coordinate conversions out of the proof.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.ModuleSheafIdentityCocycle

open SheafPullbackPathComparison

/-- A cocycle with its chosen comparison forces the original identity normalization. -/
lemma self_eq_unit {X : Scheme.{u}} (a : X ⟶ X) (ha : a = 𝟙 X)
    (h : a ≫ a = a) (M : X.Modules) (e : (pullback a).obj M ⟶ M) [IsIso e]
    (c : (pullback a).obj ((pullback a).obj M) ≅ (pullback a).obj M)
    (hc : c = (comparison a a a h).app M)
    (he : (pullback a).map e ≫ e = c.hom ≫ e) :
    e = (pullbackCongr ha).hom.app M ≫ (pullbackId X).hom.app M := by
  apply ModuleSheafIdentityRecovery.self_eq_unit a ha h M e
  rw [hc] at he
  exact he

end FLT.Mazur.ModuleSheafIdentityCocycle
