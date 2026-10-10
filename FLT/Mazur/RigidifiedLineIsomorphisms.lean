/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSheafSectionRigidity

/-!
# Uniqueness of rigidified line isomorphisms

The datum is an actual pullback trivialization. Isomorphisms preserving these
trivializations form a subsingleton when global functions descend from the base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve.LineSheafSectionRigidity
variable {X S : Scheme.{u}} (f : X ⟶ S) (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
  (hf : Function.Surjective f.appTop)

include hs hf in
/-- Equality on the section detects isomorphisms out of a line sheaf. -/
theorem iso_eq_of_pullback_hom_eq {M N : X.Modules} (hM : LocallyFreeRankOne M)
    (e e' : M ≅ N) (h : (pullback s).map e.hom = (pullback s).map e'.hom) : e = e' := by
  have hid : (pullback s).map (e.hom ≫ e'.inv) = 𝟙 _ := by
    rw [Functor.map_comp, h, ← Functor.map_comp, e'.hom_inv_id, CategoryTheory.Functor.map_id]
  have he := end_eq_id f s hs hf hM (e.hom ≫ e'.inv) hid
  apply Iso.ext
  apply (cancel_mono e'.inv).mp
  exact he.trans e'.hom_inv_id.symm

/-- Isomorphisms preserving specified actual pullback trivializations. -/
def RigidifiedIso {M N : X.Modules}
    (ρ : (pullback s).obj M ≅ structureModule S)
    (τ : (pullback s).obj N ≅ structureModule S) :=
  {e : M ≅ N // (pullback s).map e.hom ≫ τ.hom = ρ.hom}

include hs hf in
/-- Rigidified line isomorphisms are unique; no uniqueness is assumed in the datum. -/
theorem rigidifiedIso_subsingleton {M N : X.Modules} (hM : LocallyFreeRankOne M)
    (ρ : (pullback s).obj M ≅ structureModule S)
    (τ : (pullback s).obj N ≅ structureModule S) : Subsingleton (RigidifiedIso s ρ τ) := by
  refine ⟨fun e e' ↦ Subtype.ext ?_⟩
  apply iso_eq_of_pullback_hom_eq f s hs hf hM
  apply (cancel_mono τ.hom).mp
  exact e.property.trans e'.property.symm

end FLT.Mazur.FCurve.LineSheafSectionRigidity
