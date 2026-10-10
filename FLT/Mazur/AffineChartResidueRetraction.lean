/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineResidueLineRetraction
public import FLT.Mazur.ResidueNonvanishingOpenPullback

/-!
# Residue retractions on arbitrary affine schemes

The canonical affine scheme isomorphism transports actual residue
nonvanishing and the constructed sheaf retraction. Both coordinate charts
refer to tilde over the original global-section ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.AffineChartResidueRetraction
open AffineModuleGlobalSections
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} [IsAffine X]
  {M : ModuleCat.{u} Γ(X, ⊤)} {ι : Type u} (b : Module.Basis ι Γ(X, ⊤) M)

include b in
/-- Actual affine source and free ambient charts yield an actual retraction. -/
lemma exists_retraction {L N : X.Modules} (s : L ⟶ N)
    (eL : (affineTilde X).obj (ModuleCat.of Γ(X, ⊤) Γ(X, ⊤)) ≅ L)
    (eN : (affineTilde X).obj M ≅ N)
    (h : ∀ x : X, (pullback (X.fromSpecResidueField x)).map s ≠ 0) :
    ∃ r : N ⟶ L, s ≫ r = 𝟙 L := by
  let e := pullbackEquivalence X.isoSpec
  let F := e.inverse
  let _ : F.Full := inferInstanceAs e.inverse.Full
  let _ : F.Faithful := inferInstanceAs e.inverse.Faithful
  let a : tilde (ModuleCat.of Γ(X, ⊤) Γ(X, ⊤)) ≅ F.obj L :=
    e.unitIso.app _ ≪≫ F.mapIso eL
  let c : tilde M ≅ F.obj N := e.unitIso.app _ ≪≫ F.mapIso eN
  obtain ⟨r, hr⟩ := AffineResidueLineRetraction.exists_retraction b (F.map s) a c
    (ResidueNonvanishingOpenPullback.pullback X.isoSpec.inv s h)
  refine ⟨F.preimage r, ?_⟩
  apply F.map_injective
  rw [Functor.map_comp, Functor.map_preimage, CategoryTheory.Functor.map_id]
  exact hr

end FLT.Mazur.AffineChartResidueRetraction
