/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineTrivializationCocycleRecovery
public import FLT.Mazur.AmpleLineBundle

/-!
# Power sections in inverse-image cocycle coordinates

A trivialization of a specified tensor power gives a cocycle whose inverse
image recovers the corresponding power of the pulled-back line. Transporting
actual sections through this comparison preserves their generator opens.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open FLT.Mazur.FCurve.ModuleLineBundleTensorPullback

namespace FLT.Mazur.FCurve

universe u

variable {X Y : Scheme.{u}} {ι : Type u} {U : ι → Y.Opens}
  (L : Y.Modules) (n : ℕ)
  (e : ∀ i, (tensorPower L n).restrict (U i).ι ≅ structureModule (U i).toScheme)
  (hU : iSup U = ⊤) (f : X ⟶ Y)

/-- The inverse-image transition cocycle recovers the specified pulled-back tensor power. -/
def linePowerCocyclePullbackIso :
    ((lineTrivializationCocycle e).inverseImage f).sheaf ≅
      tensorPower ((pullback f).obj L) n :=
  ((lineTrivializationCocycle e).pullbackIso f hU).symm ≪≫
    (pullback f).mapIso (lineTrivializationCocycleIso e hU) ≪≫ tensorPowerIso f L n

/-- Express an actual section of the pulled-back power in inverse-image cocycle coordinates. -/
def linePowerCocycleSection (s : Γ(tensorPower ((pullback f).obj L) n, ⊤)) :
    ((lineTrivializationCocycle e).inverseImage f).sections ⊤ :=
  (linePowerCocyclePullbackIso L n e hU f).inv.app ⊤ s

/-- The transported section retains its entire nonvanishing open. -/
theorem linePowerCocycleSection_generatorOpen
    (s : Γ(tensorPower ((pullback f).obj L) n, ⊤)) :
    sectionGeneratorOpen ((lineTrivializationCocycle e).inverseImage f).sheaf
      (linePowerCocycleSection L n e hU f s) =
        sectionGeneratorOpen (tensorPower ((pullback f).obj L) n) s :=
  sectionGeneratorOpen_iso (linePowerCocyclePullbackIso L n e hU f).symm s

/-- Recover the original actual section, not just its generator open. -/
theorem linePowerCocycleSection_recover
    (s : Γ(tensorPower ((pullback f).obj L) n, ⊤)) :
    (linePowerCocyclePullbackIso L n e hU f).hom.app ⊤
      (linePowerCocycleSection L n e hU f s) = s :=
  congrArg (fun a ↦ a.app ⊤ s) (linePowerCocyclePullbackIso L n e hU f).inv_hom_id

end FLT.Mazur.FCurve
