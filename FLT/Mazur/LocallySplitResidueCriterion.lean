/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ResidueNonvanishingLocallySplit
public import FLT.Mazur.LocallySplitSheafMonomorphism
public import FLT.Mazur.ModuleSubobjectCoverEquality

/-!
# The residue criterion for local splitting of a line

A monomorphism from a line on a nonempty scheme is nonzero. Applied after
residue pullback, this gives the converse to the affine construction of local
retractions, and hence the full residue criterion for a line in a vector bundle.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits (comp_zero zero_comp)
open Scheme.Modules
namespace FLT.Mazur.LocallySplitResidueCriterion
open FCurve SplitLineAffineNeighborhood
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} {L N : X.Modules} (s : L ⟶ N)

/-- A monomorphism from a line on a nonempty scheme cannot be zero. -/
lemma line_mono_ne_zero [Nonempty X] (hL : LocallyFreeRankOne L) [Mono s] : s ≠ 0 := by
  obtain ⟨U, hx, ⟨e⟩⟩ := hL (Classical.choice ‹Nonempty X›)
  let _ : Nonempty U.toScheme := ⟨⟨_, hx⟩⟩
  let _ : Nonempty (⊤ : U.toScheme.Opens) :=
    ⟨⟨Classical.choice ‹Nonempty U.toScheme›, trivial⟩⟩
  let t := e.inv ≫ (restrictFunctor U.ι).map s
  let _ : Mono t := by
    dsimp [t]
    infer_instance
  intro hs
  have ht : t = 0 := by simp only [t, hs, Functor.map_zero, comp_zero]
  have hid : (𝟙 (structureModule U.toScheme)) = 0 :=
    (cancel_mono t).mp (by simp only [ht, comp_zero])
  have hz := congrArg (fun a : structureModule U.toScheme ⟶ structureModule U.toScheme ↦
    a.app ⊤ (1 : Γ(U.toScheme, ⊤))) hid
  exact (one_ne_zero : (1 : Γ(U.toScheme, ⊤)) ≠ 0) hz

/-- Local splitting makes the actual pulled map nonzero on every nonempty test scheme. -/
lemma pullback_ne_zero (hL : LocallyFreeRankOne L) (hs : LocallySplit s)
    {T : Scheme.{u}} [Nonempty T] (f : T ⟶ X) : (pullback f).map s ≠ 0 := by
  let _ := hs.pullback_mono s f
  exact line_mono_ne_zero _ (hL.pullback f)

/-- A line in a vector bundle splits locally exactly when every actual residue map is nonzero. -/
lemma locallySplit_iff (hL : LocallyFreeRankOne L) (hN : LocallyFiniteFree N) :
    LocallySplit s ↔ ∀ x : X, (pullback (X.fromSpecResidueField x)).map s ≠ 0 :=
  ⟨fun hs x ↦ pullback_ne_zero s hL hs (X.fromSpecResidueField x),
    ResidueNonvanishingLocallySplit.locallySplit s hL hN⟩

end FLT.Mazur.LocallySplitResidueCriterion
