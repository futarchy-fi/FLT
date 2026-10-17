/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealSheafOpenCoverDetection
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Radical ideal sheaves on open covers

Radicals commute with open restriction. An arbitrary pullback of a radical
is contained in the radical of the pulled ideal, retaining the full ideals
when that latter ideal is already radical.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.IdealSheafData
universe u
namespace FLT.Mazur.IdealSheafRadicalOpen
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y)

/-- Radical commutes with restriction to any open subscheme. -/
theorem comap_radical [IsOpenImmersion f] :
    I.radical.comap f = (I.comap f).radical := by
  ext1
  funext U
  rw [ideal_comap_of_isOpenImmersion, radical_ideal, radical_ideal,
    ideal_comap_of_isOpenImmersion, Ideal.comap_radical]

/-- Pulling back a radical introduces no equations beyond the pulled ideal's radical. -/
theorem comap_radical_le : I.radical.comap f ≤ (I.comap f).radical := by
  have he : (I.radical.comap f).radical = (I.comap f).radical := by
    rw [← vanishingIdeal_support (I := I.radical.comap f),
      ← vanishingIdeal_support (I := I.comap f), support_comap, support_comap, support_radical]
  exact he ▸ le_radical _

/-- A radical pulled ideal is unchanged if the original ideal is first radicalized. -/
theorem comap_radical_eq (h : (I.comap f).radical = I.comap f) :
    I.radical.comap f = I.comap f :=
  le_antisymm (h ▸ comap_radical_le I f) (comap_mono f (le_radical I))

/-- Radicality of the full ideal can be checked on any open cover. -/
theorem radical_eq_of_cover {X : Scheme.{u}} (I : X.IdealSheafData) (C : X.OpenCover)
    (h : ∀ j, (I.comap (C.f j)).radical = I.comap (C.f j)) : I.radical = I := by
  apply BaseAdicThickening.idealSheaf_ext_of_openCover C
  intro j
  rw [comap_radical, h]

/-- The schematic image of a reduced scheme has a radical defining ideal. -/
theorem ker_radical [IsReduced X] [QuasiCompact f] : f.ker.radical = f.ker := by
  ext1
  funext U
  change (f.ker.ideal U).radical = f.ker.ideal U
  rw [Scheme.Hom.ker_apply]
  exact Ideal.radical_eq_iff.mpr (Ideal.isRadical_bot.comap (f.app U).hom)

/-- A radical ideal sheaf defines a reduced closed subscheme. -/
theorem subscheme_isReduced {X : Scheme.{u}} (I : X.IdealSheafData)
    (h : I.radical = I) : IsReduced I.subscheme := by
  have hr (U : X.affineOpens) : (I.ideal U).IsRadical := by
    apply Ideal.radical_eq_iff.mp
    exact congrArg (fun J : X.IdealSheafData ↦ J.ideal U) h
  let _ (U : X.affineOpens) : _root_.IsReduced (Γ(X, U) ⧸ I.ideal U) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (hr U)
  let _ (U : X.affineOpens) : IsReduced (I.subschemeCover.openCover.X U) := by
    change IsReduced (Spec (.of (Γ(X, U) ⧸ I.ideal U)))
    infer_instance
  exact IsReduced.of_openCover _ I.subschemeCover.openCover

end FLT.Mazur.IdealSheafRadicalOpen
