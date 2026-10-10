/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCoverRecovery
public import FLT.Mazur.AffineQuasicoherentPullbackFaithful

/-!
# Scheme pullback faithfulness from affine faithfully flat charts

A covering family of affine base charts reduces detection of morphisms to
faithfully flat affine pullback. The square comparison transfers the given
equality along the original scheme morphism to each affine cover map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {ι : Type u}
variable (C : ι → Chart p) [∀ i, IsOpenImmersion (C i).base]
variable (hcover : ∀ x : X, ∃ i, x ∈ Set.range (C i).base)

include hcover in
/-- Affine faithfully flat charts detect maps from their original scheme pullbacks. -/
lemma chartFamily_pullback_map_injective {M N : X.Modules}
    [∀ i, ((pullback (C i).base).obj M).IsQuasicoherent]
    [∀ i, ((pullback (C i).base).obj N).IsQuasicoherent] (f g : M ⟶ N)
    (h : (pullback p).map f = (pullback p).map g) : f = g := by
  apply ModuleSheafOpenImmersionGluing.hom_ext
    (fun i ↦ Spec (C i).baseRing) (fun i ↦ (C i).base) hcover
  intro i
  apply AffineQuasicoherentPullbackFaithful.map_injective (C i).ringMap (C i).faithfullyFlat
  apply (cancel_epi ((C i).coverPullbackIso.hom.app M)).mp
  have hf := (C i).coverPullbackIso.hom.naturality f
  have hg := (C i).coverPullbackIso.hom.naturality g
  dsimp only [Functor.comp_map] at hf hg
  rw [← hf, ← hg, h]

end FLT.Mazur.SchemeAffineDescent
