/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXResidueNodeContraction
public import FLT.Mazur.WeierstrassSuccessiveXResidueNodeGeometry

/-!
# Full algebra maps of the ordered residue node charts

The actual scheme inclusions are induced by named maps on the original
tensor algebra. Their coordinate formulas retain both tangent directions.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
local notation "K" => ResidueField R
local notation "W₀" => W.map (residue R)
local notation "c" => residue R b6
local notation "T" => ScalarExtension W (π ^ k) π b3 b4 b6 K
local notation "N" => MiddleNodeOpen c
local notation "E₁" => residueMiddleFirstNodeEquiv D k hk0 hk b3 b4 b6 h3 h4
local notation "E₂" => residueMiddleSecondNodeEquiv D k hk0 hk b3 b4 b6 h3 h4

/-- Restriction of every original tensor function to the first ordered node. -/
def residueFirstNodeMap : T →ₐ[K] N :=
  (AlgEquiv.toAlgHom E₁).comp (IsScalarTower.toAlgHom K T _)

/-- Restriction to the opposite ordered node of the same tensor chart. -/
def residueSecondNodeMap : T →ₐ[K] N :=
  (AlgEquiv.toAlgHom E₂).comp (IsScalarTower.toAlgHom K T _)

/-- The named first algebra map induces precisely the actual first node chart. -/
theorem residueMiddleFirstNodeChart_eq_spec :
    residueMiddleFirstNodeChart D k hk0 hk b3 b4 b6 h3 h4 =
      Spec.map (CommRingCat.ofHom (residueFirstNodeMap D k hk0 hk b3 b4 b6 h3 h4).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- The named second algebra map induces precisely the opposite ordered node chart. -/
theorem residueMiddleSecondNodeChart_eq_spec :
    residueMiddleSecondNodeChart D k hk0 hk b3 b4 b6 h3 h4 =
      Spec.map (CommRingCat.ofHom (residueSecondNodeMap D k hk0 hk b3 b4 b6 h3 h4).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- All three original tensor coordinates retain their values on the first node. -/
theorem residueFirstNodeMap_coord (i : Fin 3) :
    residueFirstNodeMap D k hk0 hk b3 b4 b6 h3 h4 (tensorCoord W (π ^ k) π b3 b4 b6 K i) =
      ![middleNodeT (residue R W.a₁) c, middleNodeV (residue R W.a₁) c, middleNodeU c] i := by
  change E₁ (algebraMap T _ _) = _
  simp only [residueMiddleFirstNodeEquiv, AlgEquiv.trans_apply,
    residueMiddleFirstOpenEquiv, PrincipalOpenTransport.equiv_base,
    residueRetainedFiberEquiv_coord, middleFirstNodeEquiv_coord]
  rfl

/-- The opposite node keeps incidence and horizontal functions, reversing the tangent slope. -/
theorem residueSecondNodeMap_coord (i : Fin 3) :
    residueSecondNodeMap D k hk0 hk b3 b4 b6 h3 h4 (tensorCoord W (π ^ k) π b3 b4 b6 K i) =
      ![middleNodeT (residue R W.a₁) c,
        -middleNodeV (residue R W.a₁) c - algebraMap K N (residue R W.a₁),
        middleNodeU c] i := by
  change E₂ (algebraMap T _ _) = _
  fin_cases i
  · change E₂ (algebraMap T _ (tensorCoord W (π ^ k) π b3 b4 b6 K 0)) =
      middleNodeT (residue R W.a₁) c
    simp only [residueMiddleSecondNodeEquiv, AlgEquiv.trans_apply,
      residueMiddleSecondOpenEquiv, PrincipalOpenTransport.equiv_base,
      residueRetainedFiberEquiv_coord, middleSecondNodeEquiv_base,
      middleTangentSwitch_coord, Matrix.cons_val_zero, middleFirstNodeEquiv_coord]
    rfl
  · exact residueMiddleSecondNodeEquiv_v D k hk0 hk b3 b4 b6 h3 h4
  · exact residueMiddleSecondNodeEquiv_u D k hk0 hk b3 b4 b6 h3 h4

end FLT.Mazur.WeierstrassSuccessiveX
