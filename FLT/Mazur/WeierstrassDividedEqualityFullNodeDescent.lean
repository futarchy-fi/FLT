/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedEqualityTerminalNodeParameters
public import FLT.Mazur.WeierstrassModificationXFullNodeParameterDescent
public import FLT.Mazur.WeierstrassModificationXFullNodeProjectiveDescent

public import FLT.Mazur.ProjectiveLineEndpointReversal

/-!
# Full-node descent for the two scale-one terminal attachments

The complete terminal conic is used at both attachments, with its original
rational parameters, reversed endpoints and localized exterior branches.
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
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (s + 1) (Nat.lt_succ_of_le hs))
local notation "c" => residue R (Data.b6 e)
local notation "q₁" => equalityTerminalFirstNodeParameter data D s hs hk hp
local notation "q₂" => equalityTerminalSecondNodeParameter data D s hs hk hp
local notation "ρ" => ProjectiveLine.endpointReversal K
local notation "a" => residue R W.a₁
local notation "ha" => D.a₁_unit.map (residue R)
local notation "t" => Units.mk0 a (IsUnit.ne_zero ha)
local notation "s₁" => fullNodeNormalizedDenominator a c
local notation "s₂" => fullNodeNormalizedDenominator (-a) c

/-- Incoming endpoint compatibility descends on the full first original node. -/
theorem equalityCycleFullFirst_exists_unique_desc {Y : Scheme.{u}}
    (f g : ProjectiveLine.scheme K ⟶ Y)
    (w : ProjectiveLine.infinity K ≫ f = ProjectiveLine.zero K ≫ g) :
    ∃! d : Spec (.of (FullNodeOpen a c)) ⟶ Y,
      (fullNodeConicParameterIso a c ha).hom ≫ fullNodeFirstBranch a c ha ≫ d =
        q₁ ≫ ρ ≫ f ∧
      fullNodeSecondBranch a c ha ≫ d =
        NodeLocalDescent.branchOpen K (PolygonNodeEqualizer.second s₁) ≫
          ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso t).hom ≫ g := by
  apply fullNodeConicParameter_exists_unique_desc a c ha
  rw [equalityTerminalFirstNodeParameter_origin_assoc,
    ProjectiveLine.zero_endpointReversal_assoc,
    NodeLocalDescent.secondOrigin_branchOpen_assoc]
  have hz : (aeval (0 : K) : K[X] →ₐ[K] K).toRingHom = evalRingHom 0 := rfl
  simpa only [ProjectiveLine.infinitySlopeMark, ProjectiveLine.chartZero, hz,
    Category.assoc] using w.trans (ProjectiveLine.slopeNormalization_first_assoc t g).symm

/-- Outgoing compatibility retains the translated exterior at the opposite full node. -/
theorem equalityCycleFullSecond_exists_unique_desc {Y : Scheme.{u}}
    (f g : ProjectiveLine.scheme K ⟶ Y)
    (w : ProjectiveLine.zero K ≫ f = ProjectiveLine.infinity K ≫ g) :
    ∃! d : Spec (.of (FullNodeOpen (-a) c)) ⟶ Y,
      (fullNodeConicParameterIso (-a) c (ha).neg).hom ≫
          fullNodeFirstBranch (-a) c (ha).neg ≫ d = q₂ ≫ ρ ≫ f ∧
      fullNodeSecondBranch (-a) c (ha).neg ≫ d =
        NodeLocalDescent.branchOpen K (PolygonNodeEqualizer.second s₂) ≫
          Spec.map (CommRingCat.ofHom (aeval (X - C a)).toRingHom) ≫
            ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso t).hom ≫ g := by
  apply fullNodeConicParameter_exists_unique_desc (-a) c (ha).neg
  rw [equalityTerminalSecondNodeParameter_origin_assoc,
    ProjectiveLine.infinity_endpointReversal_assoc,
    NodeLocalDescent.secondOrigin_branchOpen_assoc]
  have ht := fullNode_translatedParameter_origin_assoc t
    (ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso t).hom ≫ g)
  simp only [Units.val_mk0] at ht
  rw [ht]
  simpa only [ProjectiveLine.infinitySlopeMark, Category.assoc, Units.val_mk0] using
    w.trans (ProjectiveLine.slopeNormalization_second_assoc t g).symm

end FLT.Mazur.WeierstrassDividedDepth
