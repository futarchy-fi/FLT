/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResolvedProductOpens
public import FLT.Mazur.WeierstrassSmoothAdditionCommutative

/-!
# Multiplication agrees on the two original-factor domains

On a cross-domain intersection both resolved inputs have actual original
smooth presentations. The proved original commutativity identifies the two
action formulas, with no contraction uniqueness assumption on resolved points.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus

local notation "s" => integralSmoothStructure W
local notation "t" => (U).ι ≫ base
local notation "e" => finiteOriginalToResolved hπ data j hj

omit [IsDomain R] [IsBezout R] [IsNoetherianRing R] in
/-- Original scheme-valued addition commutes on arbitrary test schemes. -/
theorem finiteOriginalPointAddition_comm {T : Scheme}
    (a b : T ⟶ (integralSmoothOpen W).toScheme)
    (h : a ≫ s = b ≫ s) :
    smoothPairPointAddition W a b h = smoothPairPointAddition W b a h.symm := by
  have hp : pullback.lift a b h ≫ smoothFactorSwap W = pullback.lift b a h.symm := by
    apply pullback.hom_ext <;>
      simp only [smoothFactorSwap, Category.assoc, pullback.lift_fst,
        pullback.lift_snd]
  rw [smoothPairPointAddition, ← smoothFactorAddition_commutative W,
    ← Category.assoc, hp]
  rfl

/-- The universal action evaluated on any test map is the same scheme-valued action. -/
@[reassoc] theorem finiteResolvedAction_point {T : Scheme} (p : T ⟶ pullback s t) :
    p ≫ finiteGlobalSmoothAction hπ data j hj =
      finiteGlobalSmoothPointAction hπ data j hj (p ≫ pullback.fst s t)
        (p ≫ pullback.snd s t) (by
          simpa only [Category.assoc] using
            (congrArg (p ≫ ·) (pullback.condition (f := s) (g := t)))) := by
  exact (finiteGlobalSmoothPointAction_comp hπ data j hj p _ _ pullback.condition).symm

/-- On an actual cross-domain overlap the two action outputs coincide. -/
theorem finiteResolvedAction_cross {T : Scheme} (p q : T ⟶ pullback s t)
    (he : p ≫ finiteResolvedInput hπ data j hj false =
      q ≫ finiteResolvedInput hπ data j hj true) :
    p ≫ finiteGlobalSmoothAction hπ data j hj = q ≫ finiteGlobalSmoothAction hπ data j hj := by
  have h₁ := congrArg (· ≫ pullback.fst t t) he
  have h₂ := congrArg (· ≫ pullback.snd t t) he
  simp only [Category.assoc, finiteResolvedRightInput_fst] at h₁
  simp only [Category.assoc, finiteResolvedRightInput_snd] at h₂
  change p ≫ finiteResolvedLeftInput hπ data j hj ≫ pullback.fst t t =
    q ≫ pullback.snd s t at h₁
  change p ≫ finiteResolvedLeftInput hπ data j hj ≫ pullback.snd t t =
    q ≫ pullback.fst s t ≫ e at h₂
  rw [finiteResolvedLeftInput_fst] at h₁
  rw [finiteResolvedLeftInput_snd] at h₂
  have hab : (p ≫ pullback.fst s t) ≫ s = (q ≫ pullback.fst s t) ≫ s := by
    calc
      _ = (p ≫ pullback.snd s t) ≫ t := by
        simpa only [Category.assoc] using congrArg (p ≫ ·) pullback.condition
      _ = _ := by
        rw [h₂]
        simp only [Category.assoc, finiteOriginalToResolved_structure]
  rw [finiteResolvedAction_point, finiteResolvedAction_point]
  have h₂' : p ≫ pullback.snd s t = (q ≫ pullback.fst s t) ≫ e :=
    h₂.trans (Category.assoc _ _ _).symm
  have h₁' : q ≫ pullback.snd s t = (p ≫ pullback.fst s t) ≫ e :=
    h₁.symm.trans (Category.assoc _ _ _).symm
  simp only [h₂', h₁']
  rw [finiteGlobalSmoothPointAction_original, finiteGlobalSmoothPointAction_original,
    finiteOriginalPointAddition_comm (W := W) (p ≫ pullback.fst s t)
      (q ≫ pullback.fst s t) hab]
  exact hab

/-- The two local actions agree on all ambient intersections of their actual open embeddings. -/
theorem finiteResolvedAction_overlap (b d : Bool) :
    pullback.fst (finiteResolvedInput hπ data j hj b) (finiteResolvedInput hπ data j hj d) ≫
        finiteGlobalSmoothAction hπ data j hj =
      pullback.snd (finiteResolvedInput hπ data j hj b) (finiteResolvedInput hπ data j hj d) ≫
        finiteGlobalSmoothAction hπ data j hj := by
  cases b <;> cases d
  · congr 1
    exact (cancel_mono (finiteResolvedInput hπ data j hj false)).mp pullback.condition
  · exact finiteResolvedAction_cross hπ data j hj _ _ pullback.condition
  · exact (finiteResolvedAction_cross hπ data j hj _ _ pullback.condition.symm).symm
  · congr 1
    exact (cancel_mono (finiteResolvedInput hπ data j hj true)).mp pullback.condition

end FLT.Mazur.WeierstrassDividedDepth
