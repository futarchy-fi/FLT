/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRankStageTestDetection
public import FLT.Mazur.SchemeEffectiveEpiSections
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Coefficient detection through a finite faithful chart and all rank orders

A finite flat surjective chart transports all-order rank vanishing to every
locally Noetherian test of the coefficient scheme. No Noetherianity of the
coefficient scheme is assumed for this test statement. When it is locally
Noetherian, all stages jointly detect its full ring of sections.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S B C Y : Scheme.{0}} [IsNoetherian S]
  (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (b : C ⟶ S) (δ : C ⟶ B) [IsFinite δ] [Flat δ] [Surjective δ]
  (ranks : Set ℕ) (hcover : ∀ x : C, ∃ m ∈ ranks, b x ∈ exactRank E m)

include hcover

/-- All original rank stages detect coefficients on every locally Noetherian scalar test. -/
theorem test_zero_of_faithful_rank_stages [IsLocallyNoetherian Y]
    (v : Y ⟶ B) (a : Γ(B, ⊤))
    (ha : ∀ m ∈ ranks, ∀ k : ℕ,
      (rankPullbackMap E b m k ≫ δ).appTop a = 0) : v.appTop a = 0 := by
  let _ : EffectiveEpi (pullback.snd δ v) := inferInstance
  apply SchemeEffectiveEpiSections.appTop_injective (pullback.snd δ v)
  rw [map_zero]
  have ht : (pullback.fst δ v).appTop (δ.appTop a) = 0 := by
    apply test_zero_of_rank_stages E b (pullback.fst δ v) ranks
      (fun y ↦ hcover (pullback.fst δ v y)) (δ.appTop a)
    intro m hm k
    simpa only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply] using ha m hm k
  have hc := congrArg (fun g : pullback δ v ⟶ B ↦ g.appTop a)
    (pullback.condition (f := δ) (g := v))
  simp only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply] at hc
  exact hc.symm.trans ht

/-- Equality on all faithful chart stages descends on each full locally Noetherian test. -/
theorem test_eq_of_faithful_rank_stages [IsLocallyNoetherian Y]
    (v : Y ⟶ B) (a c : Γ(B, ⊤))
    (hac : ∀ m ∈ ranks, ∀ k : ℕ,
      (rankPullbackMap E b m k ≫ δ).appTop a =
        (rankPullbackMap E b m k ≫ δ).appTop c) : v.appTop a = v.appTop c := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply test_zero_of_faithful_rank_stages E b δ ranks hcover v (a - c)
  intro m hm k
  rw [map_sub, hac m hm k, sub_self]

/-- Identity testing detects full coefficients on a locally Noetherian coefficient scheme. -/
theorem section_zero_of_faithful_rank_stages [IsLocallyNoetherian B]
    (a : Γ(B, ⊤))
    (ha : ∀ m ∈ ranks, ∀ k : ℕ,
      (rankPullbackMap E b m k ≫ δ).appTop a = 0) : a = 0 := by
  simpa using test_zero_of_faithful_rank_stages E b δ ranks hcover (𝟙 B) a ha

end FLT.Mazur.RelativeOrderedTuples
