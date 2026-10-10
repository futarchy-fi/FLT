/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocallySplitSheafTransport

/-!
# Monicity from actual local splitting

Local retractions cancel morphisms on a covering family. This proves
monicity of the original inclusion and of every geometric pullback.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules
universe u
namespace FLT.Mazur.SplitLineAffineNeighborhood
variable {X : Scheme.{u}} {L M : X.Modules} (s : L ⟶ M)

/-- Actual local splitting implies monicity of the original sheaf morphism. -/
lemma LocallySplit.mono (hs : LocallySplit s) : Mono s := by
  classical
  choose U hx hU using hs.restrict s
  let _ := hU
  have hcover : iSup U = ⊤ := by
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  refine ⟨fun {N} a b hab ↦ ?_⟩
  apply ModuleSheafMorphismGluing.hom_ext_restrict U hcover
  intro x
  apply (cancel_mono ((restrictFunctor (U x).ι).map s)).mp
  rw [← Functor.map_comp, ← Functor.map_comp, hab]

/-- Every geometric pullback of a locally split inclusion is monic. -/
lemma LocallySplit.pullback_mono (hs : LocallySplit s) {T : Scheme.{u}} (f : T ⟶ X) :
    Mono ((Scheme.Modules.pullback f).map s) := (hs.pullback s f).mono _

end FLT.Mazur.SplitLineAffineNeighborhood
