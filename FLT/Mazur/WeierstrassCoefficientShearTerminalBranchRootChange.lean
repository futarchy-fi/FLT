/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearTerminalBranchProjection
public import FLT.Mazur.WeierstrassSuccessiveShearTerminalBranchRootChange
public import FLT.Mazur.WeierstrassCoefficientShearRootChange

/-!
# Companion-root exchange of both entire terminal affine branches

Reconstruction through the actual original tensor chart identifies opposite
branches with their full polynomial parameters and node origins.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S) (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
variable (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4 = 0)
  (h6 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "hsNext" => show algebraMap R S (π ^ (start + (j + 1))) = 0 from by
  rw [← Nat.add_assoc, pow_succ, map_mul, hp, mul_zero]
variable (t : S)
  (ht : t ^ 2 + algebraMap R S W.a₁ * t - algebraMap R S W.a₂ = 0)
  (b : Sˣ) (hb : (b : S) = (rootShearCurve (W.map (algebraMap R S)) t).a₁)
  (hrt : r + t = -algebraMap R S W.a₁)
local notation "C" => coefficientShearRootChange hπ data S r t (j + 1) hj
local notation "G" => coefficientShearGluedIso hπ data S t (j + 1) hj
include hrt

/-- The whole first terminal branch becomes the opposite one at the companion root. -/
@[reassoc] theorem coefficientShearRootChange_terminalFirst :
    coefficientShearTerminalFirstBranch hπ data S r (j + 1) hj
        hsNext h3 h4 h6 hr a ha ≫ (C).hom =
      coefficientShearTerminalSecondBranch hπ data S t (j + 1) hj
        hsNext h3 h4 h6 ht b hb := by
  apply (cancel_mono (G).hom).mp
  rw [Category.assoc, coefficientShearRootChange_reconstruction,
    coefficientShearTerminalFirstBranch_tensor (hp := hp),
    coefficientShearTerminalSecondBranch_tensor (hp := hp)]
  rw [tensorShearTerminalFirstMap_rootChange W π (start + j)
    (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hp h3 h4 hr h6 a ha t ht b hb hrt]

/-- The whole second terminal branch becomes the opposite one at the companion root. -/
@[reassoc] theorem coefficientShearRootChange_terminalSecond :
    coefficientShearTerminalSecondBranch hπ data S r (j + 1) hj
        hsNext h3 h4 h6 hr a ha ≫ (C).hom =
      coefficientShearTerminalFirstBranch hπ data S t (j + 1) hj
        hsNext h3 h4 h6 ht b hb := by
  apply (cancel_mono (G).hom).mp
  rw [Category.assoc, coefficientShearRootChange_reconstruction,
    coefficientShearTerminalSecondBranch_tensor (hp := hp),
    coefficientShearTerminalFirstBranch_tensor (hp := hp)]
  rw [tensorShearTerminalSecondMap_rootChange W π (start + j)
    (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hp h3 h4 hr h6 a ha t ht b hb hrt]

end FLT.Mazur.WeierstrassDividedDepth
