/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.QuasiCoherentAffineBasePullback
public import FLT.Mazur.ModuleLineBundlePullback

/-!
# Quasi-coherence under arbitrary scheme pullback

The inverse images of affine opens cover the source. On each such open the
actual pullback is a pullback from an affine scheme, so its quasi-coherence
glues without affineness or finiteness assumptions on the original schemes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.QuasiCoherentSchemePullback
open FCurve QuasiCoherentAffineBasePullback

/-- Pullback along an arbitrary scheme morphism preserves quasi-coherence. -/
theorem isQuasicoherent {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) [M.IsQuasicoherent] : ((Scheme.Modules.pullback f).obj M).IsQuasicoherent := by
  have (U : Y.affineOpens) :
      (((Scheme.Modules.pullback f).obj M).over (f ⁻¹ᵁ U.1)).IsQuasicoherent := by
    let _ : IsAffine U.1.toScheme := U.2
    let _ := QuasiCoherentAffineBasePullback.pullback (f ∣_ U.1) (M.restrict U.1.ι)
    let _ := (SheafOfModules.isQuasicoherent (f ⁻¹ᵁ U.1).toScheme.ringCatSheaf).prop_of_iso
      (modulePullbackOpenIso f U.1 M).symm inferInstance
    exact over_of_restrict _ _
  apply SheafOfModules.IsQuasicoherent.of_coversTop _ (fun U : Y.affineOpens ↦ f ⁻¹ᵁ U.1)
  rw [Opens.coversTop_iff, IsOpenCover]
  ext x
  simp only [Opens.coe_iSup, Set.mem_iUnion, Opens.coe_top, Set.mem_univ, iff_true]
  obtain ⟨V, hV, hxV, _⟩ :=
    exists_isAffineOpen_mem_and_subset (show f x ∈ (⊤ : Y.Opens) from trivial)
  exact ⟨⟨V, hV⟩, hxV⟩

end FLT.Mazur.QuasiCoherentSchemePullback
