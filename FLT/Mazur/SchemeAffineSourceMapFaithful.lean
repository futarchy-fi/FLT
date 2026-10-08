/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineSourceRecovery
public import FLT.Mazur.ModuleSheafOpenImmersionGluing

/-!
# Faithfulness of gluing on a constructed source cover

Reconstruction retains the original compatible map on each source open.
If these opens cover, equality of glued maps implies equality of the
original maps. No global reconstruction isomorphism is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {ι : Type u}
variable (C : ι → SourceChart p) {M N : Y.Modules}
variable (D : SchemeGeometricDescent.Data p M) (E : SchemeGeometricDescent.Data p N)
variable [∀ i, ((pullback (C i).chart.cover).obj M).IsQuasicoherent]
variable [∀ i, ((pullback (C i).chart.cover).obj N).IsQuasicoherent]
attribute [local irreducible] openGlued Chart.sheaf sourceRecoveryIso openGluedMap

/-- Gluing distinguishes original compatible morphisms on a source-covering chart family. -/
lemma openGluedMap_injective_of_sourceCover
    (hC : iSup (fun i ↦ (C i).chart.base.opensRange) = ⊤)
    (hY : iSup (fun i ↦ (C i).sourceMap.opensRange) = ⊤)
    (f g : M ⟶ N) (hf : D.MapCompatible p E f) (hg : D.MapCompatible p E g)
    (hfg : openGluedMap (fun i ↦ (C i).chart) D E hC f hf =
      openGluedMap (fun i ↦ (C i).chart) D E hC g hg) : f = g := by
  apply ModuleSheafOpenImmersionGluing.hom_ext
    (fun i ↦ (C i).source) (fun i ↦ (C i).sourceMap)
  · intro y
    have hy : y ∈ iSup (fun i ↦ (C i).sourceMap.opensRange) := by rw [hY]; trivial
    exact Opens.mem_iSup.mp hy
  · intro i
    apply (cancel_epi (sourceRecoveryIso C D i).hom).mp
    rw [← sourceRecoveryIso_naturality C D E hC f hf,
      ← sourceRecoveryIso_naturality C D E hC g hg, hfg]

end FLT.Mazur.SchemeAffineDescent
