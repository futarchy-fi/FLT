/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedEqualityFullNodeDescent
public import FLT.Mazur.PolygonPinchingDiagram

/-!
# Local descent from the actual length-two equality family

The same terminal projective map supplies both conic parameters. The cyclic
endpoint equations supply the two original full-node descent compatibilities.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (hs : 0 + 1 ≤ n)
  (hk : 2 * (start + 0 + 1) ≤ depth) (hp : 2 * (start + 0 + 1) = depth)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (0 + 1) (Nat.lt_succ_of_le hs))
local notation "c" => residue R (Data.b6 e)
local notation "q₁" => equalityTerminalFirstNodeParameter data D 0 hs hk hp
local notation "q₂" => equalityTerminalSecondNodeParameter data D 0 hs hk hp
local notation "ρ" => ProjectiveLine.endpointReversal K
local notation "a" => residue R W.a₁
local notation "ha" => D.a₁_unit.map (residue R)
local notation "t" => Units.mk0 a (IsUnit.ne_zero ha)
local notation "s₁" => fullNodeNormalizedDenominator a c
local notation "s₂" => fullNodeNormalizedDenominator (-a) c

variable {Y : Scheme.{u}}
  (F : Fin 2 → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by decide) i))

include w in
/-- The cyclic family descends uniquely on the entire first attachment. -/
theorem zeroEqualityLengthTwoFirst_exists_unique_desc :
    ∃! d : Spec (.of (FullNodeOpen a c)) ⟶ Y,
      (fullNodeConicParameterIso a c ha).hom ≫
          fullNodeFirstBranch a c ha ≫ d = q₁ ≫ ρ ≫ F 1 ∧
      fullNodeSecondBranch a c ha ≫ d =
        NodeLocalDescent.branchOpen K (PolygonNodeEqualizer.second s₁) ≫
          ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso t).hom ≫ F 0 := by
  apply equalityCycleFullFirst_exists_unique_desc data D 0 hs hk hp (F 1) (F 0)
  simpa only [show PolygonPinching.next (by decide) (0 : Fin 2) = 1 from rfl] using
    (w 0).symm

/-- The actual first full-node map selected from cyclic descent. -/
def zeroEqualityLengthTwoFirstDesc : Spec (.of (FullNodeOpen a c)) ⟶ Y :=
  (zeroEqualityLengthTwoFirst_exists_unique_desc data D hs hk hp F w).choose

/-- The descended first conic restriction keeps the complete terminal parameter. -/
@[reassoc] theorem zeroEqualityLengthTwoFirstDesc_conic :
    (fullNodeConicParameterIso a c ha).hom ≫ fullNodeFirstBranch a c ha ≫
        zeroEqualityLengthTwoFirstDesc data D hs hk hp F w = q₁ ≫ ρ ≫ F 1 :=
  (zeroEqualityLengthTwoFirst_exists_unique_desc data D hs hk hp F w).choose_spec.1.1

/-- The descended first exterior restriction preserves its exact localization. -/
@[reassoc] theorem zeroEqualityLengthTwoFirstDesc_exterior :
    fullNodeSecondBranch a c ha ≫ zeroEqualityLengthTwoFirstDesc data D hs hk hp F w =
      NodeLocalDescent.branchOpen K (PolygonNodeEqualizer.second s₁) ≫
        ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso t).hom ≫ F 0 :=
  (zeroEqualityLengthTwoFirst_exists_unique_desc data D hs hk hp F w).choose_spec.1.2

include w in
/-- The cyclic family descends uniquely on the entire second attachment. -/
theorem zeroEqualityLengthTwoSecond_exists_unique_desc :
    ∃! d : Spec (.of (FullNodeOpen (-a) c)) ⟶ Y,
      (fullNodeConicParameterIso (-a) c (ha).neg).hom ≫
          fullNodeFirstBranch (-a) c (ha).neg ≫ d = q₂ ≫ ρ ≫ F 1 ∧
      fullNodeSecondBranch (-a) c (ha).neg ≫ d =
        NodeLocalDescent.branchOpen K (PolygonNodeEqualizer.second s₂) ≫
          Spec.map (CommRingCat.ofHom (aeval (X - C a)).toRingHom) ≫
          ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso t).hom ≫ F 0 := by
  apply equalityCycleFullSecond_exists_unique_desc data D 0 hs hk hp (F 1) (F 0)
  simpa only [show PolygonPinching.next (by decide) (1 : Fin 2) = 0 from rfl] using w 1

/-- The actual second full-node map selected from cyclic descent. -/
def zeroEqualityLengthTwoSecondDesc : Spec (.of (FullNodeOpen (-a) c)) ⟶ Y :=
  (zeroEqualityLengthTwoSecond_exists_unique_desc data D hs hk hp F w).choose

/-- The descended second conic restriction keeps the complete terminal parameter. -/
@[reassoc] theorem zeroEqualityLengthTwoSecondDesc_conic :
    (fullNodeConicParameterIso (-a) c (ha).neg).hom ≫ fullNodeFirstBranch (-a) c (ha).neg ≫
        zeroEqualityLengthTwoSecondDesc data D hs hk hp F w = q₂ ≫ ρ ≫ F 1 :=
  (zeroEqualityLengthTwoSecond_exists_unique_desc data D hs hk hp F w).choose_spec.1.1

/-- The descended second exterior restriction preserves its exact localization. -/
@[reassoc] theorem zeroEqualityLengthTwoSecondDesc_exterior :
    fullNodeSecondBranch (-a) c (ha).neg ≫ zeroEqualityLengthTwoSecondDesc data D hs hk hp F w =
      NodeLocalDescent.branchOpen K (PolygonNodeEqualizer.second s₂) ≫
          Spec.map (CommRingCat.ofHom (aeval (X - C a)).toRingHom) ≫
        ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso t).hom ≫ F 0 :=
  (zeroEqualityLengthTwoSecond_exists_unique_desc data D hs hk hp F w).choose_spec.1.2

end FLT.Mazur.WeierstrassDividedDepth
