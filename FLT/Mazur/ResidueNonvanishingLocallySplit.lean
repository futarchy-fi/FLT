/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineChartResidueRetraction
public import FLT.Mazur.AffineFiniteFreeAtlas
public import FLT.Mazur.AffineSplitLineCoordinates
public import FLT.Mazur.SplitLineAffineNeighborhood

/-!
# Local splitting from actual residue nonvanishing

A line mapping into a locally finite free sheaf splits locally if its actual
residue pullbacks are nonzero. Simultaneous affine source and ambient charts
construct retractions of the original geometric pullbacks.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.ResidueNonvanishingLocallySplit
open FCurve SplitLineAffineNeighborhood AffineModuleGlobalSections
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} {L N : X.Modules} (s : L ⟶ N)

/-- Residue nonvanishing of a line in a vector bundle constructs local sheaf splittings. -/
lemma locallySplit (hL : LocallyFreeRankOne L) (hN : LocallyFiniteFree N)
    (h : ∀ x : X, (pullback (X.fromSpecResidueField x)).map s ≠ 0) : LocallySplit s := by
  intro x
  obtain ⟨V, hxV, ⟨eV⟩⟩ := hL x
  obtain ⟨i, hxi, hiV⟩ := AffineFiniteFreeAtlas.exists_mem_le N hN hxV
  let U := i.val
  let e := ((restrictFunctorIsoPullback V.ι).app L).symm ≪≫ eV
  let a := SplitSheafLinePullback.frameOver (X.homOfLE hiV) V.ι (X.homOfLE_ι hiV) e
  let b := Finsupp.basisSingleOne (R := Γ(U.toScheme, ⊤))
    (ι := AffineFiniteFreeAtlas.coordinates N i)
  let c := AffineFreeSheafCoordinates.freeIso U.toScheme _ ≪≫
    (AffineFiniteFreeAtlas.chart N i).symm ≪≫ (restrictFunctorIsoPullback U.ι).app N
  obtain ⟨r, hr⟩ := AffineChartResidueRetraction.exists_retraction b
    ((pullback U.ι).map s) (AffineSplitLineCoordinates.sourceIso a) c
    (ResidueNonvanishingOpenPullback.pullback U.ι s h)
  exact ⟨U, hxi, IsSplitMono.mk' ⟨r, hr⟩⟩

end FLT.Mazur.ResidueNonvanishingLocallySplit
