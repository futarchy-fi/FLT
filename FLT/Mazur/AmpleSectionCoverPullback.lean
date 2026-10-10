/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleAffinePullback

/-!
# Ampleness from pulled-back affine generator opens

A generating family in one positive tensor power proves ampleness after
pullback whenever its inverse-image generator opens are affine. This
separates the section argument from the construction of those affine opens.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules FLT.Mazur.FCurve.ModuleLineBundleTensorPullback

universe u v

namespace FLT.Mazur.FCurve

/-- An affine cover by pulled-back positive-power sections proves ampleness. -/
theorem ampleLineBundle_pullback_of_section_cover {X Y : Scheme.{u}} [CompactSpace Y]
    {L : X.Modules} (hL : LocallyFreeRankOne L) (j : Y ⟶ X) {n : ℕ} (hn : 0 < n)
    {ι : Type v} (t : ι → Γ(tensorPower L n, ⊤))
    (ht : ⨆ i, sectionGeneratorOpen (tensorPower L n) (t i) = ⊤)
    (ha : ∀ i, IsAffineOpen (j ⁻¹ᵁ sectionGeneratorOpen (tensorPower L n) (t i))) :
    AmpleLineBundle ((pullback j).obj L) := by
  refine ⟨inferInstance, hL.pullback j, fun y ↦ ?_⟩
  have hy : j y ∈ ⨆ i, sectionGeneratorOpen (tensorPower L n) (t i) := by
    rw [ht]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
  let e := tensorPowerIso j L n
  refine ⟨n, hn, e.hom.app ⊤ (pullGlobal j (tensorPower L n) (t i)), ?_, ?_⟩
  · rw [sectionGeneratorOpen_iso, sectionGeneratorOpen_pullGlobal (hL.tensorPower n)]
    exact hi
  · rw [sectionGeneratorOpen_iso, sectionGeneratorOpen_pullGlobal (hL.tensorPower n)]
    exact ha i

end FLT.Mazur.FCurve
