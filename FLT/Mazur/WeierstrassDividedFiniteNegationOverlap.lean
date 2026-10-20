/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteNegationCover

/-!
# Exact agreement of the finite projective negatives

The unchanged infinity pullback gives uniqueness whenever the reference map
lands in that chart. This suffices on cross-chart intersections; no global
contraction extensionality for a modified scheme is assumed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "M" => finiteGlobalModel hπ data j hj
local notation "c" => finiteGlobalContraction hπ data j hj
local notation "i" => finiteNegationInclusion hπ data j hj
local notation "e" => finiteNegationDomainIso hπ data j hj

/-- A contraction equality determines the lift when its reference lies at infinity. -/
theorem finiteInfinity_contraction_ext {T : Scheme} (f : T ⟶ M)
    (g : T ⟶ chartScheme W 1) (h : f ≫ c = g ≫ integralCurveChart W 1) :
    f = g ≫ finiteInfinityChart hπ data j hj := by
  let H := finiteInfinity_isPullback hπ data j hj
  have h₁ := H.lift_fst g f h.symm
  have h₂ := H.lift_snd g f h.symm
  have hl : H.lift g f h.symm = g := by
    simpa only [Category.comp_id] using h₁
  rw [hl] at h₂
  exact h₂.symm

/-- Each complete local negative with its actual global target. -/
def finiteGlobalNegationLocal (b : Bool) : finiteNegationDomain hπ data j hj b ⟶ M :=
  (e b).hom ≫ i b

/-- The local formulas contract to the same originally chosen cubic negative. -/
@[reassoc] theorem finiteGlobalNegationLocal_contraction (b : Bool) :
    finiteGlobalNegationLocal hπ data j hj b ≫ c =
      i b ≫ c ≫ integralCurveNegation W := by
  rw [finiteGlobalNegationLocal, Category.assoc, finiteNegationDomainIso_contraction]

/-- Both local negatives agree on every actual intersection in the finite global model. -/
theorem finiteGlobalNegationLocal_overlap (b d : Bool) :
    pullback.fst (i b) (i d) ≫ finiteGlobalNegationLocal hπ data j hj b =
      pullback.snd (i b) (i d) ≫ finiteGlobalNegationLocal hπ data j hj d := by
  have hc : (pullback.fst (i b) (i d) ≫
        finiteGlobalNegationLocal hπ data j hj b) ≫ c =
      (pullback.snd (i b) (i d) ≫ finiteGlobalNegationLocal hπ data j hj d) ≫ c := by
    simp only [Category.assoc, finiteGlobalNegationLocal_contraction]
    simpa only [Category.assoc] using
      congrArg (· ≫ c ≫ integralCurveNegation W) (pullback.condition (f := i b) (g := i d))
  cases b <;> cases d
  · have hp : pullback.fst (i false) (i false) = pullback.snd (i false) (i false) :=
      (cancel_mono (i false)).mp pullback.condition
    rw [hp]
  · change _ = (pullback.snd _ _ ≫ (e true).hom ≫ infinityNegationInclusion W) ≫
      finiteInfinityChart hπ data j hj
    apply finiteInfinity_contraction_ext
    simpa only [finiteGlobalNegationLocal, finiteNegationInclusion, Category.assoc,
      finiteInfinityChart_contraction] using hc
  · symm
    change _ = (pullback.fst _ _ ≫ (e true).hom ≫ infinityNegationInclusion W) ≫
      finiteInfinityChart hπ data j hj
    apply finiteInfinity_contraction_ext
    simpa only [finiteGlobalNegationLocal, finiteNegationInclusion, Category.assoc,
      finiteInfinityChart_contraction] using hc.symm
  · have hp : pullback.fst (i true) (i true) = pullback.snd (i true) (i true) :=
      (cancel_mono (i true)).mp pullback.condition
    rw [hp]

end FLT.Mazur.WeierstrassDividedDepth
