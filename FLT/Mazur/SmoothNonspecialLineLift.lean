/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalPointConditionRank

/-!
# Smooth relative lifts of nonspecial geometric lines

Starting with a relative line whose geometric restriction is acyclic and has
a section, impose universal point conditions. Every step changes the base by
the smooth curve morphism and retains the original geometric fiber square.
The output is an actual relative line, not an assumed extension of a field line.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor universalPointConditionLine

variable {k : Type} [Field k] [IsAlgClosed k]
  {Y : Scheme} [IsReduced Y] (q : Y ⟶ Spec (.of k))
  [IsProper q] [SmoothOfRelativeDimension 1 q]

/-- Successive point conditions construct a smooth relative lift with nonspecial restriction. -/
theorem exists_smooth_nonspecial_line_lift {X S : Scheme} (f : X ⟶ S)
    [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    {p : Y ⟶ X} {g : Spec (.of k) ⟶ S} (H : IsPullback p q f g)
    (L : X.Modules) (hL : LocallyFreeRankOne L)
    [Subsingleton (ModuleScalarH q ((Scheme.Modules.pullback p).obj L) 1)]
    (hp : 0 < Module.finrank k (ModuleScalarH q ((Scheme.Modules.pullback p).obj L) 0)) :
    ∃ (U Z : Scheme) (a : U ⟶ S) (b : Z ⟶ X) (r : Z ⟶ U)
      (u : Spec (.of k) ⟶ U) (v : Y ⟶ Z) (N : Z.Modules),
      Smooth a ∧ IsPullback b r f a ∧ IsPullback v q r u ∧
      u ≫ a = g ∧ v ≫ b = p ∧ LocallyFreeRankOne N ∧
      Subsingleton (ModuleScalarH q ((Scheme.Modules.pullback v).obj N) 1) ∧
      Module.finrank k (ModuleScalarH q ((Scheme.Modules.pullback v).obj N) 0) = 1 := by
  generalize hn : Module.finrank k (ModuleScalarH q ((Scheme.Modules.pullback p).obj L) 0) = n
    at *
  induction n using Nat.strong_induction_on generalizing X S with
  | h n ih =>
    by_cases h1 : n = 1
    · exact ⟨S, X, 𝟙 S, 𝟙 X, f, g, p, L, inferInstance,
        IsPullback.of_horiz_isIso ⟨by simp⟩, H, by simp, by simp, hL,
        inferInstance, hn.trans h1⟩
    obtain ⟨s, hs, hz, hr⟩ := exists_universal_point_rank_drop f H L hL (hn.symm ▸ hp)
    let N := universalPointConditionLine f L
    let v := pointConditionMap f H s hs
    have hN : LocallyFreeRankOne N := universalPointConditionLine_rankOne f L hL
    let _ : Subsingleton (ModuleScalarH q ((Scheme.Modules.pullback v).obj N) 1) := hz
    let _ : SmoothOfRelativeDimension 1 (pullback.snd f f) :=
      MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) f f inferInstance
    change Module.finrank k (ModuleScalarH q ((Scheme.Modules.pullback v).obj N) 0) + 1 =
      Module.finrank k (ModuleScalarH q ((Scheme.Modules.pullback p).obj L) 0) at hr
    rw [hn] at hr
    have hm : Module.finrank k (ModuleScalarH q ((Scheme.Modules.pullback v).obj N) 0) < n :=
      by omega
    have hmpos : 0 < Module.finrank k
        (ModuleScalarH q ((Scheme.Modules.pullback v).obj N) 0) := by
      omega
    obtain ⟨U, Z, a, b, r, u, w, M, ha, HB, HW, hu, hw, hM, hV, hR⟩ :=
      ih _ hm (pullback.snd f f) (pointConditionMap_isPullback f H s hs) N hN rfl hmpos
    let _ : Smooth f := SmoothOfRelativeDimension.smooth 1 f
    let _ := ha
    refine ⟨U, Z, a ≫ f, b ≫ pullback.fst f f, r, u, w, M, inferInstance,
      HB.paste_horiz (IsPullback.of_hasPullback f f), HW, ?_, ?_, hM, hV, hR⟩
    · rw [← Category.assoc, hu, pointCondition_parameter_over f H s hs]
    · rw [← Category.assoc, hw, pointConditionMap_fst]

end FLT.Mazur.FCurve
