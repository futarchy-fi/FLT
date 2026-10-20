/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageCoreRelationPullback
public import FLT.Mazur.RankStageFiniteCoreDetection

/-!
# Full mixed equations from actual original core coefficient values

Two original section candidates with the same invariant core values satisfy
every original mixed relation equation. Tests retain the entire mixed source,
all core orders and nilpotents. Existence of those section candidates is not
assumed by a structure or inferred from formal compatibility alone.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- A section identity on a full pullback evaluates on every original test square. -/
theorem corePullback_section_value {A B C T : Scheme.{0}} (f : C ⟶ A) (g : B ⟶ A)
    (s : Γ(B, ⊤)) (w : Γ(C, ⊤))
    (hs : (pullback.snd f g).appTop s = (pullback.fst f g).appTop w)
    (c : T ⟶ C) (b : T ⟶ B) (h : c ≫ f = b ≫ g) : b.appTop s = c.appTop w := by
  have he := congrArg (pullback.lift c b h).appTop hs
  change (pullback.lift c b h ≫ pullback.snd f g).appTop s =
    (pullback.lift c b h ≫ pullback.fst f g).appTop w at he
  simpa only [pullback.lift_snd, pullback.lift_fst] using he

variable {D A B B' T : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance mixedDetectionOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance mixedDetectionOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance mixedDetectionOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local irreducible] rankStageCore rankStageCoreOriginalMap
variable (g : B ⟶ A) (g' : B' ⟶ A) (u : T ⟶ B) (v : T ⟶ B') (δ : T ⟶ D)
  (hu : δ ≫ p = u ≫ g) (hv : δ ≫ q = v ≫ g')
  (n k : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
local notation "f" => rankStageCoreOriginalMap e n a ha k

include hu hv in
/-- One core value preserves both independent original mixed endpoints on its full test. -/
theorem mixed_equation_on_core (s : Γ(B, ⊤)) (t : Γ(B', ⊤))
    (w : rankStageCoreInvariants e n a ha k)
    (hs : (pullback.snd f g).appTop s = (pullback.fst f g).appTop w.val)
    (ht : (pullback.snd f g').appTop t = (pullback.fst f g').appTop w.val) :
    (pullback.snd f (δ ≫ p)).appTop (u.appTop s) =
      (pullback.snd f (δ ≫ p)).appTop (v.appTop t) := by
  let z := pullback.snd f (δ ≫ p)
  let c := pullback.fst f (δ ≫ p)
  have hc : (z ≫ δ) ≫ p = c ≫ f := by
    rw [Category.assoc]
    exact pullback.condition.symm
  obtain ⟨c', hc', hw⟩ := rankStageCore_original_invariant_test e n a ha k c (z ≫ δ) hc w
  have hs' := corePullback_section_value f g s w.val hs c (z ≫ u) (by
    rw [Category.assoc, ← hu]
    exact pullback.condition)
  have ht' := corePullback_section_value f g' t w.val ht c' (z ≫ v) (by
    rw [← hc', Category.assoc, hv, Category.assoc])
  exact hs'.trans (hw.trans ht'.symm)

variable [IsLocallyNoetherian T] {ι : Type}
  (ns : ι → ℕ) (as bs : ι → Γ(A, ⊤))
  (has : ∀ i, A.basicOpen (as i) ≤ rankImageOpen (Over.mk p) (ns i))
  (h : ∀ i k, rankThickeningMap (Over.mk p) (ns i) k ⁻¹ᵁ A.basicOpen (bs i) ≤
    rankStageCore e (ns i) (as i) (has i) k)
  (hcover : ∀ x : T, ∃ i, (δ ≫ p) x ∈ exactRank (Over.mk p) (ns i) ∧
    (δ ≫ p) x ∈ A.basicOpen (bs i))

include hu hv h hcover in
/-- All core orders prove the full mixed equation on the unchanged original source. -/
theorem mixed_equation_of_core_values (s : Γ(B, ⊤)) (t : Γ(B', ⊤))
    (w : ∀ i k, rankStageCoreInvariants e (ns i) (as i) (has i) k)
    (hs : ∀ i k,
      (pullback.snd (rankStageCoreOriginalMap e (ns i) (as i) (has i) k) g).appTop s =
        (pullback.fst (rankStageCoreOriginalMap e (ns i) (as i) (has i) k) g).appTop (w i k).val)
    (ht : ∀ i k,
      (pullback.snd (rankStageCoreOriginalMap e (ns i) (as i) (has i) k) g').appTop t =
        (pullback.fst (rankStageCoreOriginalMap e (ns i) (as i) (has i) k) g').appTop (w i k).val) :
    u.appTop s = v.appTop t := by
  apply section_eq_of_selected_core_orders e (δ ≫ p) ns as bs has h hcover
  intro i k
  exact mixed_equation_on_core e g g' u v δ hu hv (ns i) k (as i) (has i)
    s t (w i k) (hs i k) (ht i k)

end FLT.Mazur.EquivalenceRelationOrderedFrames
