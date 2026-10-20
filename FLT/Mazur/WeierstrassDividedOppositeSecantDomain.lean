/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecantSmoothPoint

/-!
# Explicit opposite-branch points of the new resolved multiplication domain

At split nodal residue coefficients, any two nonzero distinct divided
abscissae on opposite tangent branches construct a point of the new open.
Both actual finite-model inputs are retained by the projection identities.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R K : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [Field K] [Algebra R K] {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "d" => data ⟨j, Nat.lt_succ_of_le hj⟩
local notation "s" => π ^ (start + j)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "V" => finiteResolvedSecantOutputOpen hπ data j hj
variable (hs : algebraMap R K (π ^ (start + j)) = 0)
  (h2 : algebraMap R K W.a₂ = 0)
  (h3 : algebraMap R K (data ⟨j, Nat.lt_succ_of_le hj⟩).b3 = 0)
  (h4 : algebraMap R K (data ⟨j, Nat.lt_succ_of_le hj⟩).b4 = 0)
  (h6 : algebraMap R K (data ⟨j, Nat.lt_succ_of_le hj⟩).b6 = 0)
  (ht : algebraMap R K W.a₁ ≠ 0) (u v : K) (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
local notation "a" => splitBranchEvaluation W s (d).b3 (d).b4 (d).b6 hs h2 h3 h4 h6 false u
local notation "c" => splitBranchEvaluation W s (d).b3 (d).b4 (d).b6 hs h2 h3 h4 h6 true v

/-- Opposite punctured branches explicitly give a point in the actual resolved addition domain. -/
def finiteOppositeBranchSecantPoint : Spec (.of K) ⟶ (V).toScheme :=
  finiteDividedSecantSmoothPoint hπ data j hj a c
    (by rw [splitBranchEvaluation_derivative]; exact mul_ne_zero ht hu)
    (by rw [splitBranchEvaluation_derivative]; exact neg_ne_zero.mpr (mul_ne_zero ht hv))
    (by simp only [splitBranchEvaluation_x]; exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr huv))
    hs h2 ht (by simpa only [splitBranchEvaluation_x] using hu)
    (by simpa only [splitBranchEvaluation_x] using hv)
    (by simp only [splitBranchEvaluation_y, Bool.false_eq_true, ↓reduceIte])
    (by simp only [splitBranchEvaluation_y, splitBranchEvaluation_x, ↓reduceIte])

/-- The first projection is the exact zero-ordinate divided branch in the original finite model. -/
@[reassoc] theorem finiteOppositeBranchSecantPoint_fst :
    finiteOppositeBranchSecantPoint hπ data j hj hs h2 h3 h4 h6 ht u v hu hv huv ≫
        finiteResolvedSecantDomainMap hπ data j hj ≫ pullback.fst t t ≫ (U).ι =
      Spec.map (CommRingCat.ofHom (a).toRingHom) ≫ finiteSecantDividedChart hπ data j hj := by
  simp only [finiteOppositeBranchSecantPoint, finiteDividedSecantSmoothPoint_input_assoc,
    finiteDividedSmoothPair, pullback.lift_fst_assoc, finiteDividedSmoothInput_inclusion]

/-- The second projection is the exact opposite tangent branch in that same finite model. -/
@[reassoc] theorem finiteOppositeBranchSecantPoint_snd :
    finiteOppositeBranchSecantPoint hπ data j hj hs h2 h3 h4 h6 ht u v hu hv huv ≫
        finiteResolvedSecantDomainMap hπ data j hj ≫ pullback.snd t t ≫ (U).ι =
      Spec.map (CommRingCat.ofHom (c).toRingHom) ≫ finiteSecantDividedChart hπ data j hj := by
  simp only [finiteOppositeBranchSecantPoint, finiteDividedSecantSmoothPoint_input_assoc,
    finiteDividedSmoothPair, pullback.lift_snd_assoc, finiteDividedSmoothInput_inclusion]

/-- The original cubic contraction of the first input is unchanged. -/
@[reassoc] theorem finiteOppositeBranchSecantPoint_fst_contraction :
    finiteOppositeBranchSecantPoint hπ data j hj hs h2 h3 h4 h6 ht u v hu hv huv ≫
        finiteResolvedSecantDomainMap hπ data j hj ≫ pullback.fst t t ≫ (U).ι ≫
          finiteGlobalContraction hπ data j hj =
      Spec.map (CommRingCat.ofHom (a).toRingHom) ≫ toCurve d := by
  rw [finiteOppositeBranchSecantPoint_fst_assoc, finiteSecantDividedChart_contraction]

/-- The original cubic contraction of the second input is unchanged as well. -/
@[reassoc] theorem finiteOppositeBranchSecantPoint_snd_contraction :
    finiteOppositeBranchSecantPoint hπ data j hj hs h2 h3 h4 h6 ht u v hu hv huv ≫
        finiteResolvedSecantDomainMap hπ data j hj ≫ pullback.snd t t ≫ (U).ι ≫
          finiteGlobalContraction hπ data j hj =
      Spec.map (CommRingCat.ofHom (c).toRingHom) ≫ toCurve d := by
  rw [finiteOppositeBranchSecantPoint_snd_assoc, finiteSecantDividedChart_contraction]

end FLT.Mazur.WeierstrassDividedDepth
