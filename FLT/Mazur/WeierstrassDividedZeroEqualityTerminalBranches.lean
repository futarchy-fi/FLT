/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedEqualityTerminalNodeParameters
public import FLT.Mazur.WeierstrassDividedZeroEqualityCycle

/-!
# The full terminal node branches in the original equality-depth cycle

The single terminal projective component is reversed in cyclic order. Both
actual parameter opens retain this reversal and their original tangent sign.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (s + 1) (Nat.lt_succ_of_le hs))
local notation "c" => residue R (Data.b6 e)
local notation "q₁" => equalityTerminalFirstNodeParameter data D s hs hk hp
local notation "q₂" => equalityTerminalSecondNodeParameter data D s hs hk hp
local notation "ρ" => ProjectiveLine.endpointReversal K
local notation "Z" => zeroEqualityCycleComponent hπ data D s hs hstart hk hp

/-- The first terminal parameter enters the reversed cyclic component at its original node. -/
@[reassoc] theorem zeroEqualityCycleComponent_terminal_first_parameter (hpos : 0 < s) :
    q₁ ≫ ρ ≫ (Z ⟨s + 1, by omega⟩).left =
      middleParameterConicBranch c ≫
        olderGlobalResidueFirstNode hπ data D s hs 0 hs (by omega) hk := by
  have H := congrArg Over.Hom.left
    (zeroEqualityCycleComponent_terminal hπ data D s hs hstart hk hp)
  rw [H]
  change q₁ ≫ ρ ≫ ρ ≫ laurentTerminalProjectiveComponent hπ data D s hs hk hp = _
  rw [← Category.assoc ρ ρ, ProjectiveLine.endpointReversal_involutive, Category.id_comp]
  exact equalityTerminalFirstNodeParameter_branch hπ data D s hs hk hp (by omega)

/-- The opposite terminal parameter keeps its sign and the same reversed cyclic component. -/
@[reassoc] theorem zeroEqualityCycleComponent_terminal_second_parameter (hpos : 0 < s) :
    Spec.map (CommRingCat.ofHom (conicParameterNeg c).toRingHom) ≫
        q₂ ≫ ρ ≫ (Z ⟨s + 1, by omega⟩).left =
      middleParameterConicBranch c ≫
        olderGlobalResidueSecondNode hπ data D s hs 0 hs (by omega) hk := by
  have H := congrArg Over.Hom.left
    (zeroEqualityCycleComponent_terminal hπ data D s hs hstart hk hp)
  rw [H]
  change _ ≫ q₂ ≫ ρ ≫ ρ ≫ laurentTerminalProjectiveComponent hπ data D s hs hk hp = _
  rw [← Category.assoc ρ ρ, ProjectiveLine.endpointReversal_involutive, Category.id_comp]
  exact equalityTerminalSecondNodeParameter_branch hπ data D s hs hk hp (by omega)

end FLT.Mazur.WeierstrassDividedDepth
