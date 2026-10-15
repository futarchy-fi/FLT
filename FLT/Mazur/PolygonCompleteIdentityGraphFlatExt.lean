/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphFlat
public import FLT.Mazur.PolygonCompleteFlatContractionExt
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Flat original-input tests determine graph points uniquely

The contraction detects graph maps on every flat original-base test scheme.
A flat base change of the graph projection is therefore a monomorphism;
properness and schematic dominance then make it an isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "P" => completeIdentityActionProduct K n h 0
local notation "H" => completeIdentityActionGraphClosure K n h
local notation "p" => completeIdentityActionGraphProjection K n h
local notation "l" => completeIdentityActionGraphLift K n h
local notation "s" => completeIdentityActionSecond K n h
local notation "π" => exactVeroneseProjToBase K n h

/-- The actual projection is schematically dominant, not merely topologically surjective. -/
instance completeIdentityActionGraphProjection_schematic : IsSchemeTheoreticallyDominant (p) := by
  constructor
  apply le_bot_iff.mp
  calc
    (p).ker ≤ (completeIdentityActionSmoothToGraph K n h ≫ (p)).ker :=
      (completeIdentityActionSmoothToGraph K n h).le_ker_comp _
    _ = (completeIdentityActionSmoothOpen K n h).ι.ker := by
      rw [completeIdentityActionSmoothToGraph_projection]
    _ = ⊥ := Scheme.Hom.ker_eq_bot _

/-- Flat test schemes have at most one graph map above each original input map. -/
theorem completeIdentityActionGraph_flat_ext {T : Scheme}
    (t : T ⟶ Spec (.of (PowerSeries K))) [Flat t]
    (f g : T ⟶ (H)) (hf : f ≫ (p) ≫ (s) ≫ (π) = t)
    (he : f ≫ (p) = g ≫ (p)) : f = g := by
  have hl : f ≫ (l) = g ≫ (l) := by
    apply completeFlat_contraction_ext K n h 0 t
    · rw [Category.assoc, completeIdentityActionGraphLift_structure, hf]
    · rw [Category.assoc, completeIdentityActionGraphLift_structure,
        ← Category.assoc g (p), ← he, Category.assoc, hf]
    · rw [Category.assoc, completeIdentityActionGraphLift_contraction,
        Category.assoc, completeIdentityActionGraphLift_contraction,
        ← Category.assoc, he, Category.assoc]
  apply (cancel_mono (completeIdentityActionGraphInclusion K n h)).mp
  apply pullback.hom_ext
  · exact he
  · exact hl

/-- Flatness of a graph base change rules out multiple graph points over original inputs. -/
theorem completeIdentityActionGraphBaseChange_mono {T : Scheme}
    (v : T ⟶ (P)) [Flat (v ≫ (s) ≫ (π))]
    [Flat (pullback.snd (p) v)] : Mono (pullback.snd (p) v) := by
  let q := pullback.snd (p) v
  let r := pullback.fst (p) v
  let a := pullback.fst q q
  let b := pullback.snd q q
  have he : a ≫ r ≫ (p) = b ≫ r ≫ (p) := by
    rw [pullback.condition, ← Category.assoc a q, pullback.condition, Category.assoc]
  have hr : a ≫ r = b ≫ r := by
    apply completeIdentityActionGraph_flat_ext K n h (a ≫ q ≫ v ≫ (s) ≫ (π))
    · dsimp only [r, q]
      simp only [Category.assoc, pullback.condition_assoc]
    · simpa only [Category.assoc] using he
  have hab : a = b := by
    apply pullback.hom_ext
    · exact hr
    · exact pullback.condition
  constructor
  intro Z c d hcd
  let k := pullback.lift c d hcd
  calc
    c = k ≫ a := (pullback.lift_fst _ _ _).symm
    _ = k ≫ b := congrArg (k ≫ ·) hab
    _ = d := pullback.lift_snd _ _ _

/-- Every flat original-input base change on which the graph is flat has an actual inverse. -/
theorem completeIdentityActionGraphBaseChange_isIso {T : Scheme}
    (v : T ⟶ (P)) [Flat v] [Flat (pullback.snd (p) v)] :
    IsIso (pullback.snd (p) v) := by
  let _ := completeIdentityActionGraphBaseChange_mono K n h v
  let _ : IsClosedImmersion (pullback.snd (p) v) :=
    (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨inferInstance, inferInstance⟩
  exact IsClosedImmersion.isIso_iff_ker_eq_bot.mpr (Scheme.Hom.ker_eq_bot _)

end FLT.Mazur.PolygonInfinitesimalStages
