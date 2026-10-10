/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ResiduePullbackNonvanishingTransport
public import FLT.Mazur.AffineModuleGlobalSections

/-!
# Residue nonvanishing on open charts

Residue field maps of open immersions are isomorphisms. Consequently the
actual residue nonvanishing condition survives geometric open pullback.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits (comp_zero zero_comp)
open Scheme.Modules
namespace FLT.Mazur.ResidueNonvanishingOpenPullback
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Composite and iterated pullback agree on vanishing through the canonical comparison. -/
lemma comp_map_eq_zero_iff {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M N : Z.Modules} (s : M ⟶ N) :
    (pullback (f ≫ g)).map s = 0 ↔ (pullback f).map ((pullback g).map s) = 0 := by
  let e := pullbackComp f g
  have hn := e.hom.naturality s
  change (pullback f).map ((pullback g).map s) ≫ e.hom.app N =
    e.hom.app M ≫ (pullback (f ≫ g)).map s at hn
  constructor
  · intro h
    apply (cancel_mono (e.hom.app N)).mp
    rw [hn, h, comp_zero, zero_comp]
  · intro h
    apply (cancel_epi (e.hom.app M)).mp
    rw [← hn, h, zero_comp, comp_zero]

/-- Open pullback preserves nonvanishing at every actual residue spectrum. -/
lemma pullback {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {M N : Y.Modules} (s : M ⟶ N)
    (h : ∀ y : Y, (Scheme.Modules.pullback (Y.fromSpecResidueField y)).map s ≠ 0)
    (x : X) :
    (Scheme.Modules.pullback (X.fromSpecResidueField x)).map
      ((Scheme.Modules.pullback f).map s) ≠ 0 := by
  intro hz
  have hc := (comp_map_eq_zero_iff (X.fromSpecResidueField x) f s).mpr hz
  rw [← f.SpecMap_residueFieldMap_fromSpecResidueField x] at hc
  have hi := (comp_map_eq_zero_iff (Spec.map (f.residueFieldMap x))
    (Y.fromSpecResidueField (f x)) s).mp hc
  let e := asIso (Spec.map (f.residueFieldMap x))
  let _ : (Scheme.Modules.pullback e.hom).Faithful :=
    inferInstanceAs (AffineModuleGlobalSections.pullbackEquivalence e).functor.Faithful
  apply h (f x)
  apply (Scheme.Modules.pullback e.hom).map_injective
  simpa only [e, asIso_hom, Functor.map_zero] using hi

end FLT.Mazur.ResidueNonvanishingOpenPullback
