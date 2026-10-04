/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineBundleSectionOpenPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Ample line bundles under affine pullback

Affine morphisms preserve the affine section-open definition of ampleness.
In particular this applies to closed immersions. The proof transports actual
sections of tensor powers and their exact generator opens.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
variable {X Y : Scheme.{u}} {L : X.Modules}

/-- Every natural tensor power of an invertible sheaf is invertible. -/
theorem LocallyFreeRankOne.tensorPower (hL : LocallyFreeRankOne L) (n : ℕ) :
    LocallyFreeRankOne (tensorPower L n) := by
  induction n with
  | zero => exact structureModule_locallyFreeRankOne
  | succ n hn => exact ModuleSheafTensor.LocallyRankOne.tensor hL hn

/-- Open restriction of a section has the exact inverse-image generator open. -/
lemma sectionGeneratorOpen_restrict (hL : LocallyFreeRankOne L)
    (j : Y ⟶ X) [IsOpenImmersion j] (s : Γ(L, ⊤)) :
    sectionGeneratorOpen (L.restrict j)
      (L.presheaf.map (homOfLE (show j ''ᵁ ⊤ ≤ ⊤ from le_top)).op s) =
      j ⁻¹ᵁ sectionGeneratorOpen L s := by
  rw [← sectionGeneratorOpen_pullGlobal hL j s, ← pullGlobal_restrict]
  exact (sectionGeneratorOpen_iso ((restrictFunctorIsoPullback j).app L) _).symm

/-- Affine pullback preserves ampleness, including over nonreduced bases. -/
theorem AmpleLineBundle.pullback_affine (hL : AmpleLineBundle L)
    (f : Y ⟶ X) [IsAffineHom f] : AmpleLineBundle ((pullback f).obj L) := by
  let := hL.1
  refine ⟨QuasiCompact.compactSpace_of_compactSpace f, hL.2.1.pullback f, fun y ↦ ?_⟩
  obtain ⟨n, hn, s, hy, hs⟩ := hL.2.2 (f y)
  let e := tensorPowerIso f L n
  refine ⟨n, hn, e.hom.app ⊤ (pullGlobal f (tensorPower L n) s), ?_, ?_⟩
  · rw [sectionGeneratorOpen_iso, sectionGeneratorOpen_pullGlobal (hL.2.1.tensorPower n)]
    exact hy
  · rw [sectionGeneratorOpen_iso, sectionGeneratorOpen_pullGlobal (hL.2.1.tensorPower n)]
    exact hs.preimage f

end FLT.Mazur.FCurve
