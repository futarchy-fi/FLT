/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXZeroConicBoundary
public import FLT.Mazur.WeierstrassModificationXFullNodeConicBranch
public import FLT.Mazur.WeierstrassConicZeroAffineParameter

/-!
# Original Laurent punctures in the full start-zero node charts

Both normalized punctures factor through the actual localized conic branch.
At depth zero the second full node already incorporates its tangent sign.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : k = 0) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
  (hc : residue R b6 = 0)
local notation "K" => ResidueField R
local notation "W₀" => W.map (residue R)
local notation "c" => residue R b6
local notation "ha" => D.a₁_unit.map (residue R)
local notation "E" => zeroResidueConicBoundaryIso D k hk0 hk b3 b4 b6 h3 h4
local notation "t" => coord W (π ^ k) π b3 b4 b6 0
local notation "s₁" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (conicBoundaryFirst W₀ c ha hc)))
local notation "s₂" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (conicBoundarySecond W₀ c ha hc)))
local notation "a" => residue R W.a₁
local notation "A" => conicZeroAffineIso c hc
local notation "V" => zeroResidueFiberIso D k hk0 hk b3 b4 b6 h3 h4

/-- The first original puncture passes through the complete localized first conic branch. -/
@[reassoc] theorem zeroResidueConicFirstPuncture_node :
    s₁ ≫ Iso.hom E ≫ PrincipalOpenTensor.inclusion K t =
      ProjectiveLine.overlapLeft K ≫ Iso.hom A ≫
        Iso.hom (fullNodeConicParameterIso a c ha) ≫ fullNodeFirstBranch a c ha ≫
          fullFirstNodeChart a c ha ≫ Iso.hom V := by
  have H : s₁ ≫ PrincipalOpenTransport.inclusion (conicT a c) =
      Spec.map (CommRingCat.ofHom (conicZeroPuncture c hc).toRingHom) ≫
        (conicFirstParameterIso a c ha).inv ≫ conicFirstOpenImmersion a c :=
    conicBoundaryFirst_inclusion W₀ c ha hc
  rw [zeroResidueConicBoundaryIso_inclusion, ← Category.assoc, H, Category.assoc,
    fullNodeFirstBranch_firstChart_assoc a c ha,
    conicZeroAffineIso_puncture_assoc c hc]
  simp only [zeroResidueConicImmersion, Category.assoc]

/-- The opposite original puncture retains the full node's own signed conic parameter. -/
@[reassoc] theorem zeroResidueConicSecondPuncture_node :
    s₂ ≫ Iso.hom E ≫ PrincipalOpenTensor.inclusion K t =
      ProjectiveLine.overlapLeft K ≫ Iso.hom A ≫
        Iso.hom (fullNodeConicParameterIso (-a) c (IsUnit.neg ha)) ≫
          fullNodeFirstBranch (-a) c (IsUnit.neg ha) ≫
            fullSecondNodeChart a c ha ≫ Iso.hom V := by
  have H : s₂ ≫ PrincipalOpenTransport.inclusion (conicT a c) =
      Spec.map (CommRingCat.ofHom (conicZeroPuncture c hc).toRingHom) ≫
        (conicSecondParameterIso a c ha).inv ≫ conicSecondOpenImmersion a c :=
    conicBoundarySecond_inclusion W₀ c ha hc
  rw [zeroResidueConicBoundaryIso_inclusion, ← Category.assoc, H, Category.assoc,
    fullNodeFirstBranch_secondChart_assoc a c ha,
    conicZeroAffineIso_puncture_assoc c hc]
  simp only [zeroResidueConicImmersion, Category.assoc]

end FLT.Mazur.WeierstrassSuccessiveX
