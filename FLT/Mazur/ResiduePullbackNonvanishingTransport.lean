/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineModulePullbackSections
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Transport of actual residue nonvanishing

A zero pullback stays zero under further geometric base change. This compares
scheme residue fields with ideal residue fields without choosing coordinates
on the sheaves or replacing their actual pullback functors.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits (comp_zero zero_comp)
open Scheme.Modules
namespace FLT.Mazur.ResiduePullbackNonvanishingTransport
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Further geometric pullback preserves vanishing of the original map. -/
lemma comp_map_eq_zero {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M N : Z.Modules} (s : M ⟶ N) (h : (pullback g).map s = 0) :
    (pullback (f ≫ g)).map s = 0 := by
  let e := pullbackComp f g
  apply (cancel_epi (e.hom.app M)).mp
  have hn := e.hom.naturality s
  change (pullback f).map ((pullback g).map s) ≫ e.hom.app N =
    e.hom.app M ≫ (pullback (f ≫ g)).map s at hn
  rw [← hn, h, Functor.map_zero, zero_comp, comp_zero]

/-- Nonvanishing after a composite implies nonvanishing at its intermediate pullback. -/
lemma map_ne_zero_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M N : Z.Modules} (s : M ⟶ N) (h : (pullback (f ≫ g)).map s ≠ 0) :
    (pullback g).map s ≠ 0 := fun hz ↦ h (comp_map_eq_zero f g s hz)

/-- Actual scheme residue nonvanishing implies ideal-residue-spectrum nonvanishing. -/
lemma ideal_residue_map_ne_zero {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    (s : M ⟶ N) (p : Spec R)
    (h : (pullback ((Spec R).fromSpecResidueField p)).map s ≠ 0) :
    (pullback (Spec.map (CommRingCat.ofHom
      (algebraMap R p.asIdeal.ResidueField)))).map s ≠ 0 := by
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField] at h
  exact map_ne_zero_of_comp _ _ s h

end FLT.Mazur.ResiduePullbackNonvanishingTransport
