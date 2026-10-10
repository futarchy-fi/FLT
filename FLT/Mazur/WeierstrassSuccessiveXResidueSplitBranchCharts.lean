/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleSplitBranchCharts
public import FLT.Mazur.WeierstrassSuccessiveXResidueNodeMaps
public import FLT.Mazur.WeierstrassSuccessiveXResidueMiddleComponents

/-!
# Original split branches in the tensor residue fiber

Both full principal-open node charts retain their conic and horizontal
component maps under the actual tensor comparison.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory Polynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
local notation "K" => ResidueField R
local notation "W₀" => W.map (residue R)
local notation "c" => residue R b6
local notation "a" => residue R W.a₁
local notation "h2" => Iff.mpr (residue_eq_zero_iff _) D.a₂_mem
local notation "ha" => D.a₁_unit.map (residue R)
local notation "A" => Coordinate W₀ 0 0 0 0 c
local notation "T" => ScalarExtension W (π ^ k) π b3 b4 b6 K
local notation "E" => residueRetainedIso D k hk0 hk b3 b4 b6 h3 h4
local notation "J₁" => PrincipalOpenTransport.chart
  (coord W₀ 0 0 0 0 c 1 + algebraMap K A (WeierstrassCurve.a₁ W₀)) (middleFirstNodeEquiv W₀ c h2 ha)
local notation "J₂" => PrincipalOpenTransport.chart (-coord W₀ 0 0 0 0 c 1)
  (middleSecondNodeEquiv W₀ c h2 ha)

/-- The first tensor node chart is the original full tangent chart after tensor transport. -/
theorem residueMiddleFirstNodeChart_retained :
    residueMiddleFirstNodeChart D k hk0 hk b3 b4 b6 h3 h4 = J₁ ≫ (E).hom := by
  rw [residueMiddleFirstNodeChart_eq_spec, middleFirstNodeChart_eq_spec W₀ c h2 ha]
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro q
  change residueMiddleFirstNodeEquiv D k hk0 hk b3 b4 b6 h3 h4
    (algebraMap T _ q) = _
  simp only [residueMiddleFirstNodeEquiv, AlgEquiv.trans_apply,
    residueMiddleFirstOpenEquiv, PrincipalOpenTransport.equiv_base]
  exact middleFirstToNode_base W₀ c h2 ha _

/-- The opposite tensor node chart keeps the original tangent involution. -/
theorem residueMiddleSecondNodeChart_retained :
    residueMiddleSecondNodeChart D k hk0 hk b3 b4 b6 h3 h4 = J₂ ≫ (E).hom := by
  rw [residueMiddleSecondNodeChart_eq_spec, middleSecondNodeChart_eq_spec W₀ c h2 ha]
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro q
  change residueMiddleSecondNodeEquiv D k hk0 hk b3 b4 b6 h3 h4
    (algebraMap T _ q) = _
  simp only [residueMiddleSecondNodeEquiv, AlgEquiv.trans_apply,
    residueMiddleSecondOpenEquiv, PrincipalOpenTransport.equiv_base,
    middleSecondNodeEquiv_base]
  exact middleFirstToNode_base W₀ c h2 ha _

local notation "C₁" => residueSuccessiveConicImmersion D k hk0 hk b3 b4 b6 h3 h4
local notation "L" => residueSuccessiveLineImmersion D k hk0 hk b3 b4 b6 h3 h4

/-- The first conic branch is its original full parameter in the tensor fiber. -/
@[reassoc] theorem residueMiddleFirstNodeChart_conicBranch (hc : residue R b6 = 0) :
    middleNodeFirstBranch c hc ≫ residueMiddleFirstNodeChart D k hk0 hk b3 b4 b6 h3 h4 =
      (conicZeroAffineIso c hc).hom ≫ (conicFirstParameterIso a c ha).inv ≫
        conicFirstOpenImmersion a c ≫ C₁ := by
  rw [residueMiddleFirstNodeChart_retained, ← Category.assoc,
    middleNodeFirstBranch_firstChart]
  simp only [residueSuccessiveConicImmersion, Category.assoc, WeierstrassCurve.map]

/-- The opposite conic branch preserves the required negative second parameter. -/
@[reassoc] theorem residueMiddleSecondNodeChart_conicBranch (hc : residue R b6 = 0) :
    middleNodeFirstBranch c hc ≫ residueMiddleSecondNodeChart D k hk0 hk b3 b4 b6 h3 h4 =
      Spec.map (CommRingCat.ofHom (aeval (-X : K[X])).toRingHom) ≫
        (conicZeroAffineIso c hc).hom ≫ (conicSecondParameterIso a c ha).inv ≫
          conicSecondOpenImmersion a c ≫ C₁ := by
  rw [residueMiddleSecondNodeChart_retained, ← Category.assoc,
    middleNodeFirstBranch_secondChart]
  simp only [residueSuccessiveConicImmersion, Category.assoc, WeierstrassCurve.map]

/-- The first horizontal branch retains its original tensor line map. -/
@[reassoc] theorem residueMiddleFirstNodeChart_lineBranch (hc : residue R b6 = 0) :
    middleNodeSecondBranch c hc ≫ residueMiddleFirstNodeChart D k hk0 hk b3 b4 b6 h3 h4 =
      L 0 (middle_first_root W₀) := by
  rw [residueMiddleFirstNodeChart_retained, ← Category.assoc,
    middleNodeSecondBranch_firstChart]
  rfl

/-- The opposite horizontal branch retains its original translated slope. -/
@[reassoc] theorem residueMiddleSecondNodeChart_lineBranch (hc : residue R b6 = 0) :
    middleNodeSecondBranch c hc ≫ residueMiddleSecondNodeChart D k hk0 hk b3 b4 b6 h3 h4 =
      L (-a) (middle_second_root W₀) := by
  rw [residueMiddleSecondNodeChart_retained, ← Category.assoc,
    middleNodeSecondBranch_secondChart]
  rfl

end FLT.Mazur.WeierstrassSuccessiveX
