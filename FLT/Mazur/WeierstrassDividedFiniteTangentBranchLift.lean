/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentBranchScheme
public import FLT.Mazur.WeierstrassDividedFiniteSecantInput

/-!
# Strict-branch tangent outputs in the actual finite model

Use the universal flat two-input source and insert the constructed divided
output into the same finite model. Its original contraction is the exact
tangent output, including when that output is originally singular.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation WeierstrassIntegralChart
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  (a2 b4' b6' : R)
  (h2 : W.a₂ = π ^ (start + j) * a2)
  (h4' : (data ⟨j, Nat.lt_succ_of_le hj⟩).b4 = π ^ (start + j) * b4')
  (h6' : (data ⟨j, Nat.lt_succ_of_le hj⟩).b6 = π ^ (start + j) * b6')
local notation "d" => data ⟨j, Nat.lt_succ_of_le hj⟩
local notation "s" => π ^ (start + j)
local notation "a" => dividedPairLeft W s (d).b3 (d).b4 (d).b6
local notation "c" => dividedPairRight W s (d).b3 (d).b4 (d).b6
local notation "B" => DividedTangentBranchRing W s (d).b3 (d).b4 (d).b6 a c
local notation "e" => dividedTangentBranchRestriction W s (d).b3 (d).b4 (d).b6 a c
local notation "v" => dividedTangentBranchLift W s (d).b3 (d).b4 (d).b6 a c
  a2 b4' b6' (isRegular_iff_ne_zero.mpr (pow_ne_zero _ hπ)) h2
  (d).factor3 (d).factor4 (d).factor6 h4' h6'

/-- The constructed branch output in the same entire finite model as both inputs. -/
def finiteTangentBranchLift : Spec (.of B) ⟶ finiteGlobalModel hπ data j hj :=
  v ≫ finiteSecantDividedChart hπ data j hj

/-- Its original contraction is the actual tangent output on this genuine branch domain. -/
@[reassoc] theorem finiteTangentBranchLift_contraction :
    finiteTangentBranchLift hπ data j hj a2 b4' b6' h2 h4' h6' ≫
        finiteGlobalContraction hπ data j hj =
      Spec.map (CommRingCat.ofHom (e).toRingHom) ≫
        dividedTangentToCurve W s (d).b3 (d).b4 (d).b6 a c
          (d).factor3 (d).factor4 (d).factor6 := by
  rw [finiteTangentBranchLift, Category.assoc, finiteSecantDividedChart_contraction]
  exact dividedTangentBranchLift_contraction ..

/-- The output retains the original coefficient point on the entire branch domain. -/
@[reassoc] theorem finiteTangentBranchLift_structure :
    finiteTangentBranchLift hπ data j hj a2 b4' b6' h2 h4' h6' ≫
        finiteGlobalStructure hπ data j hj = Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [finiteTangentBranchLift, Category.assoc, finiteSecantDividedChart_structure]
  exact specAlgHom_structure _

end FLT.Mazur.WeierstrassDividedDepth
