/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXResidueSplitBranchCharts
public import FLT.Mazur.WeierstrassSuccessiveXResidueConicBoundaryGeometry
public import FLT.Mazur.WeierstrassConicZeroAffineParameter

/-!
# Original Laurent punctures inside the complete retained node charts

The normalized conic boundary restricts to the actual affine node branches.
The opposite branch requires negation before entering its original node chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- Negating the affine parameter twice preserves every regular function. -/
@[reassoc] theorem affineParameterNeg_comp (K : Type u) [Field K] :
    Spec.map (CommRingCat.ofHom (aeval (-X : K[X])).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (aeval (-X : K[X])).toRingHom) =
        𝟙 (ProjectiveLine.chart K) := by
  rw [← Spec.map_comp]
  have h : (aeval (-X : K[X])).comp (aeval (-X : K[X])) = AlgHom.id K K[X] := by
    ext
    simp
  change Spec.map (CommRingCat.ofHom
    ((aeval (-X : K[X])).comp (aeval (-X : K[X]))).toRingHom) = _
  rw [h]
  exact Spec.map_id _

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
  (hc : residue R b6 = 0)
local notation "K" => ResidueField R
local notation "W₀" => W.map (residue R)
local notation "c" => residue R b6
local notation "ha" => D.a₁_unit.map (residue R)
local notation "E" => residueConicBoundaryIso D k hk0 hk b3 b4 b6 h3 h4
local notation "t" => coord W (π ^ k) π b3 b4 b6 0
local notation "s₁" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (conicBoundaryFirst W₀ c ha hc)))
local notation "s₂" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (conicBoundarySecond W₀ c ha hc)))
local notation "neg" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (aeval (-X : K[X]))))

/-- The first original Laurent puncture is the first node's ordinary conic branch. -/
@[reassoc] theorem residueConicFirstPuncture_node :
    s₁ ≫ Iso.hom E ≫ PrincipalOpenTensor.inclusion K t =
      ProjectiveLine.overlapLeft K ≫ middleNodeFirstBranch c hc ≫
        residueMiddleFirstNodeChart D k hk0 hk b3 b4 b6 h3 h4 := by
  rw [residueConicBoundaryIso_inclusion, ← Category.assoc,
    conicBoundaryFirst_inclusion, Category.assoc,
    residueMiddleFirstNodeChart_conicBranch, conicZeroAffineIso_puncture_assoc]
  rfl

/-- The second original Laurent puncture enters the opposite node with negative parameter. -/
@[reassoc] theorem residueConicSecondPuncture_node :
    s₂ ≫ Iso.hom E ≫ PrincipalOpenTensor.inclusion K t =
      ProjectiveLine.overlapLeft K ≫ neg ≫ middleNodeFirstBranch c hc ≫
        residueMiddleSecondNodeChart D k hk0 hk b3 b4 b6 h3 h4 := by
  rw [residueConicBoundaryIso_inclusion, ← Category.assoc,
    conicBoundarySecond_inclusion, Category.assoc,
    residueMiddleSecondNodeChart_conicBranch, affineParameterNeg_comp_assoc,
    conicZeroAffineIso_puncture_assoc]
  rfl

end FLT.Mazur.WeierstrassSuccessiveX
