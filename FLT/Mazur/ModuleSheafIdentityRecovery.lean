/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SheafPullbackPathComparison

/-!
# The identity normalization forced by an invertible cocycle

An invertible self-transition over the identity cannot change coordinates:
its composition law forces the canonical identity pullback comparison.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.ModuleSheafIdentityRecovery

open SheafPullbackPathComparison

/-- An invertible idempotent pullback transition is the canonical identity comparison. -/
lemma self_eq_unit {X : Scheme.{u}} (a : X ⟶ X) (ha : a = 𝟙 X)
    (h : a ≫ a = a) (M : X.Modules) (e : (pullback a).obj M ⟶ M) [IsIso e]
    (he : (pullback a).map e ≫ e = (comparison a a a h).hom.app M ≫ e) :
    e = (pullbackCongr ha).hom.app M ≫ (pullbackId X).hom.app M := by
  subst a
  have hh := (cancel_mono e).mp he
  rw [comparison_comp_id] at hh
  let _ : (pullback (𝟙 X)).Faithful := Functor.Faithful.of_iso (pullbackId X).symm
  simpa [pullbackCongr] using (pullback (𝟙 X)).map_injective hh

/-- Recovery through a self-inclusion cancels against its canonical unit comparison. -/
lemma recovery_self {X Y : Scheme.{u}} (i : Y ⟶ X) (a : Y ⟶ Y)
    (ha : a = 𝟙 Y) (h : a ≫ i = i) (G : X.Modules) (N : Y.Modules)
    (e : (pullback i).obj G ⟶ N) :
    (comparison a i i h).inv.app G ≫ (pullback a).map e ≫
      (pullbackCongr ha).hom.app N ≫ (pullbackId Y).hom.app N = e := by
  subst a
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp]
  rw [(pullbackId Y).hom.naturality, ← comparison_id_comp i G]
  exact (comparison (𝟙 Y) i i h).inv_hom_id_app_assoc G e

end FLT.Mazur.ModuleSheafIdentityRecovery
