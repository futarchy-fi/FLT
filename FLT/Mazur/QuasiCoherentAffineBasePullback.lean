/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSourcePullbackSections

/-!
# Quasi-coherent pullback from an affine base

Quasi-coherence descends from actual restrictions to affine opens. The
source restriction comparison then proves that any pullback from an affine
base preserves quasi-coherence, without assuming the source is affine.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules

universe u

namespace FLT.Mazur.QuasiCoherentAffineBasePullback

/-- Transporting from an open subscheme to its over site preserves quasi-coherence. -/
lemma overEquiv_inverse {X : Scheme.{u}} (U : X.Opens) (N : U.toScheme.Modules)
    [N.IsQuasicoherent] : ((overEquiv U).inverse.obj N).IsQuasicoherent := by
  have : U.overEquivalence.functor.PreservesOneHypercovers.{u}
      ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology ↥U) :=
    Functor.PreservesOneHypercovers.of_coverPreserving
      (Functor.IsDenseSubsite.coverPreserving _ _ _)
  exact SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint U.overEquivalence.functor
    (U.sheafRestrictSheafEquivOver.app X.ringCatSheaf).inv
    (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf)

/-- A quasi-coherent actual open restriction gives quasi-coherence on the over site. -/
lemma over_of_restrict {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    [(M.restrict U.ι).IsQuasicoherent] : (M.over U).IsQuasicoherent := by
  let e : (overEquiv U).inverse.obj (M.restrict U.ι) ≅ M.over U :=
    (overEquiv U).inverse.mapIso ((overFunctorEquiv U).app M).symm ≪≫
      ((overEquiv U).unitIso.app (M.over U)).symm
  exact (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over U)).prop_of_iso e
    (overEquiv_inverse U (M.restrict U.ι))

/-- Quasi-coherence can be checked on all actual affine open restrictions. -/
lemma of_affineOpen_restrict {X : Scheme.{u}} (M : X.Modules)
    (hM : ∀ U : X.affineOpens, (M.restrict U.1.ι).IsQuasicoherent) : M.IsQuasicoherent := by
  have (U : X.affineOpens) : (M.over U.1).IsQuasicoherent := by
    let _ := hM U
    exact over_of_restrict M U.1
  apply SheafOfModules.IsQuasicoherent.of_coversTop M (fun U : X.affineOpens ↦ U.1)
  rw [Opens.coversTop_iff, IsOpenCover]
  ext x
  simp only [Opens.coe_iSup, Set.mem_iUnion, Opens.coe_top, Set.mem_univ, iff_true]
  obtain ⟨V, hV, hxV, _⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  exact ⟨⟨V, hV⟩, hxV⟩

/-- Pullback from an affine base is quasi-coherent on an arbitrary source scheme. -/
theorem pullback {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y)
    (M : Y.Modules) [M.IsQuasicoherent] : ((Scheme.Modules.pullback f).obj M).IsQuasicoherent := by
  apply of_affineOpen_restrict
  intro U
  exact (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).prop_of_iso
    ((AffineSourcePullbackSections.restrictionIso f U.1.ι).app M).symm
    (AffineQuasiCoherentBaseChange.isQuasicoherent_pullback (U.1.ι ≫ f) M)

end FLT.Mazur.QuasiCoherentAffineBasePullback
