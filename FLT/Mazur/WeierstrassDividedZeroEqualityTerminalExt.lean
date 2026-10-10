/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityTerminalBranches
public import FLT.Mazur.WeierstrassDividedZeroEqualityTerminalLineBranches
public import FLT.Mazur.WeierstrassSuccessiveXMiddleParameterDescent

/-!
# The terminal pair of original node opens detects morphisms

The whole terminal parameter open and the signed horizontal line determine
maps on each terminal attachment. The terminal constant need not vanish.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth) (hpos : 0 < s)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (s + 1) (Nat.lt_succ_of_le hs))
local notation "c" => residue R (Data.b6 e)
local notation "q₁" => equalityTerminalFirstNodeParameter data D s hs hk hp
local notation "q₂" => equalityTerminalSecondNodeParameter data D s hs hk hp
local notation "ρ" => ProjectiveLine.endpointReversal K
local notation "ν" => Spec.map
  (CommRingCat.ofHom (RingEquiv.toRingHom (AlgEquiv.toRingEquiv (conicParameterNeg c))))
local notation "G₁" => olderGlobalResidueFirstNode hπ data D s hs 0 hs (by omega) hk
local notation "G₂" => olderGlobalResidueSecondNode hπ data D s hs 0 hs (by omega) hk
local notation "tangent" => WeierstrassDilatation.residueTangentUnit D
variable {Y : Scheme.{u}}
  (f g : finiteGlobalTensorModel hπ data (ResidueField R) (s + 1) hs ⟶ Y)
  (h : ∀ i, (zeroEqualityCycleComponent hπ data D s hs hstart hk hp i).left ≫ f =
    (zeroEqualityCycleComponent hπ data D s hs hstart hk hp i).left ≫ g)

include h in
/-- The first terminal attachment is determined by the two complete cyclic components. -/
theorem zeroEqualityCycleComponent_terminal_first_hom_ext : G₁ ≫ f = G₁ ≫ g := by
  apply middleParameter_hom_ext c
  · have H := congrArg (fun q => q₁ ≫ ρ ≫ q) (h ⟨s + 1, by omega⟩)
    simpa only [zeroEqualityCycleComponent_terminal_first_parameter_assoc hπ data D s hs
      hstart hk hp hpos] using H
  · have H := congrArg (fun q => ProjectiveLine.left K ≫ q) (h ⟨s, by omega⟩)
    simp only [zeroEqualityCycleComponent_terminal_first_lineBranch_assoc hπ data D s hs
      hstart hk hp hpos] at H
    exact middleNode_cancel_chartScaling (tangent)⁻¹ _ _ H

include h in
/-- The opposite terminal attachment retains both its tangent sign and full parameter. -/
theorem zeroEqualityCycleComponent_terminal_second_hom_ext : G₂ ≫ f = G₂ ≫ g := by
  apply middleParameter_hom_ext c
  · have H := congrArg (fun q => ν ≫ q₂ ≫ ρ ≫ q) (h ⟨s + 1, by omega⟩)
    simpa only [zeroEqualityCycleComponent_terminal_second_parameter_assoc hπ data D s hs
      hstart hk hp hpos] using H
  · have H := congrArg (fun q => ProjectiveLine.right K ≫ q) (h ⟨s + 2, by omega⟩)
    simp only [zeroEqualityCycleComponent_terminal_second_lineBranch_assoc hπ data D s hs
      hstart hk hp hpos] at H
    exact middleNode_cancel_chartScaling (-tangent)⁻¹ _ _ H

end FLT.Mazur.WeierstrassDividedDepth
