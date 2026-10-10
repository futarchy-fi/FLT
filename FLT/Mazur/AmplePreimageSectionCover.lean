/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleSectionCoverPullback

/-!
# Ampleness from a cover only after pullback

A finite-stage section family need not cover its stage. It suffices that its
nonvanishing opens become an affine cover on the chosen refinement.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules FLT.Mazur.FCurve.ModuleLineBundleTensorPullback

namespace FLT.Mazur.FCurve

universe u v

/-- A cover by inverse images of power-section opens proves ampleness on the source. -/
theorem ampleLineBundle_of_preimage_section_cover {X Y : Scheme.{u}} [CompactSpace Y]
    {L : X.Modules} (hL : LocallyFreeRankOne L) (j : Y ⟶ X) {n : ℕ} (hn : 0 < n)
    {ι : Type v} (t : ι → Γ(tensorPower L n, ⊤))
    (ht : (⨆ i, j ⁻¹ᵁ sectionGeneratorOpen (tensorPower L n) (t i)) = ⊤)
    (ha : ∀ i, IsAffineOpen (j ⁻¹ᵁ sectionGeneratorOpen (tensorPower L n) (t i))) :
    AmpleLineBundle ((pullback j).obj L) := by
  refine ⟨inferInstance, hL.pullback j, fun y ↦ ?_⟩
  have hy : y ∈ ⨆ i, j ⁻¹ᵁ sectionGeneratorOpen (tensorPower L n) (t i) := by
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
