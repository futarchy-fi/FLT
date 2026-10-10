/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSheafGlobalEndomorphisms
public import FLT.Mazur.LocallySplitSheafTransport

/-!
# Locally split inclusions between line bundles

A split inclusion between lines is invertible: its projector is a scalar,
and faithful scalar action on the source forces that scalar to be one.
Local splitting then gives an actual global isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.SplitLineAffineNeighborhood
open FCurve FCurve.ModuleSheafScalarEndomorphisms IdealPowerScalarLift IdealAdicQuotient
variable {X : Scheme.{u}} {L N : X.Modules} (s : L ⟶ N)

/-- A retraction of a map between lines is also a right inverse. -/
theorem line_retraction_inverse (hL : LocallyFreeRankOne L) (hN : LocallyFreeRankOne N)
    (r : N ⟶ L) (hr : s ≫ r = 𝟙 L) : r ≫ s = 𝟙 N := by
  let _ : IsSplitMono s := IsSplitMono.mk' ⟨r, hr⟩
  obtain ⟨a, ha⟩ := (scalarEnd_bijective hN).surjective (r ≫ s)
  have h : scalarEnd L a = 𝟙 L := by
    apply (cancel_mono s).mp
    rw [scalarEnd_naturality, ha, ← Category.assoc, hr, Category.id_comp]
  have h1 : a = 1 := (scalarEnd_bijective hL).injective
    (h.trans (scalarEnd_one L).symm)
  rw [← ha, h1, scalarEnd_one]

/-- Split inclusions between lines are actual isomorphisms on any scheme. -/
theorem isIso_of_splitMono_line (hL : LocallyFreeRankOne L) (hN : LocallyFreeRankOne N)
    [IsSplitMono s] : IsIso s :=
  ⟨⟨retraction s, IsSplitMono.id s,
    line_retraction_inverse s hL hN (retraction s) (IsSplitMono.id s)⟩⟩

/-- Local splitting suffices; no global frame or global retraction is required. -/
theorem LocallySplit.isIso (hs : LocallySplit s)
    (hL : LocallyFreeRankOne L) (hN : LocallyFreeRankOne N) : IsIso s := by
  choose U hx hu using hs
  apply ModuleSheafOpenIsoDetection.isIso_of_openCover s U (fun x ↦ ⟨x, hx x⟩)
  intro x
  let _ := hu x
  let _ := isIso_of_splitMono_line ((Scheme.Modules.pullback (U x).ι).map s)
    (hL.pullback _) (hN.pullback _)
  let a := restrictFunctorIsoPullback (U x).ι
  have he : (restrictFunctor (U x).ι).map s =
      a.hom.app L ≫ (Scheme.Modules.pullback (U x).ι).map s ≫ a.inv.app N := by
    rw [← a.hom.naturality_assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [he]
  infer_instance

end FLT.Mazur.SplitLineAffineNeighborhood
