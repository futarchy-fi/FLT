/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedEqualityTerminalZeroParameters
public import FLT.Mazur.WeierstrassDividedZeroExteriorNodeBranches
public import FLT.Mazur.WeierstrassDividedZeroEqualityCycle

/-!
# The two original attachments of the length-two equality cycle

The same complete terminal component meets the exterior twice. Both full
conic parameters and both localized exterior branches remain unchanged.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (hs : 0 + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + 0 + 1) ≤ depth)
  (hp : 2 * (start + 0 + 1) = depth)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk 1 (by omega))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 e)
local notation "ha" => D.a₁_unit.map (residue R)
local notation "u" => Units.mk0 a (IsUnit.ne_zero ha)
local notation "G₁" => olderGlobalZeroFirstNode hπ data D 0 hs 0 hs
  hstart hk
local notation "G₂" => olderGlobalZeroSecondNode hπ data D 0 hs 0 hs
  hstart hk
local notation "Z" => zeroEqualityCycleComponent hπ data D 0 hs hstart hk hp
local notation "ρ" => Iso.inv (ProjectiveLine.endpointReversalIso K)

/-- The first full conic parameter belongs to the single reversed terminal component. -/
@[reassoc] theorem zeroEqualityCycleComponent_lengthTwo_first_conic :
    equalityTerminalFirstNodeParameter data D 0 hs hk hp ≫ ρ ≫ (Z 1).left =
      (fullNodeConicParameterIso a c ha).hom ≫
        fullNodeFirstBranch a c ha ≫ G₁ := by
  rw [show (1 : Fin (2 * 0 + 2)) = ⟨0 + 1, by omega⟩ from rfl,
    zeroEqualityCycleComponent_terminal]
  change _ ≫ (ProjectiveLine.endpointReversalIso K).inv ≫
    (ProjectiveLine.endpointReversalIso K).hom ≫ _ = _
  rw [Iso.inv_hom_id_assoc]
  exact equalityTerminalFirstNodeParameter_zero_branch hπ data D 0 hs hk hp
    (by simpa using hstart)

/-- The second full conic parameter belongs to the single reversed terminal component. -/
@[reassoc] theorem zeroEqualityCycleComponent_lengthTwo_second_conic :
    equalityTerminalSecondNodeParameter data D 0 hs hk hp ≫ ρ ≫ (Z 1).left =
      (fullNodeConicParameterIso (-a) c (ha).neg).hom ≫
        fullNodeFirstBranch (-a) c (ha).neg ≫ G₂ := by
  rw [show (1 : Fin (2 * 0 + 2)) = ⟨0 + 1, by omega⟩ from rfl,
    zeroEqualityCycleComponent_terminal]
  change _ ≫ (ProjectiveLine.endpointReversalIso K).inv ≫
    (ProjectiveLine.endpointReversalIso K).hom ≫ _ = _
  rw [Iso.inv_hom_id_assoc]
  exact equalityTerminalSecondNodeParameter_zero_branch hπ data D 0 hs hk hp
    (by simpa using hstart)

/-- The first attachment's other branch is the exact localized original exterior component. -/
@[reassoc] theorem zeroEqualityCycleComponent_lengthTwo_first_exterior :
    NodeLocalDescent.branchOpen K
        (PolygonNodeEqualizer.second (fullNodeNormalizedDenominator a c)) ≫
        ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso u).hom ≫ (Z 0).left =
      fullNodeSecondBranch a c ha ≫ G₁ := by
  rw [zeroEqualityCycleComponent_exterior]
  change _ ≫ _ ≫ _ ≫ finalZeroExteriorComponent hπ data D 0 hs hstart hk = _
  rw [finalZeroExteriorComponent, zeroRetainedOrientedToGlobal_first_nodeBranch_assoc]
  simp only [eqToHom_refl, Category.comp_id]

/-- The second attachment keeps the translated exterior branch and the original denominator. -/
@[reassoc] theorem zeroEqualityCycleComponent_lengthTwo_second_exterior :
    NodeLocalDescent.branchOpen K
        (PolygonNodeEqualizer.second (fullNodeNormalizedDenominator (-a) c)) ≫
        Spec.map (CommRingCat.ofHom (aeval (X - C a)).toRingHom) ≫
        ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso u).hom ≫ (Z 0).left =
      fullNodeSecondBranch (-a) c (ha).neg ≫ G₂ := by
  rw [zeroEqualityCycleComponent_exterior]
  change _ ≫ _ ≫ _ ≫ _ ≫ finalZeroExteriorComponent hπ data D 0 hs hstart hk = _
  rw [finalZeroExteriorComponent, zeroRetainedOrientedToGlobal_second_nodeBranch_assoc]
  simp only [eqToHom_refl, Category.comp_id]

end FLT.Mazur.WeierstrassDividedDepth
