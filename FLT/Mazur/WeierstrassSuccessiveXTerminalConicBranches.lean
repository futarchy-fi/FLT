/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXTerminalConicParameters
public import FLT.Mazur.WeierstrassSuccessiveXConicPuncturedParameters
public import FLT.Mazur.PolygonNodePresentation

/-!
# Ordered terminal node branches on the original conic punctures

The first conic puncture meets the second node branch with reciprocal
parameter, and the second conic puncture meets the first node branch.
The equalities hold on the whole coordinate algebras.
-/

@[expose] public noncomputable section
open IsLocalRing
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
local notation "T" => WeierstrassDilatation.ScalarExtension W (π ^ (k + 1)) b3 b4 b6 K
local notation "e₀" => WeierstrassDilatation.residueRetainedTensorEquiv
  b3 b4 b6 D (k + 1) (Nat.zero_lt_succ k) hk h3 h4
local notation "e" => AlgEquiv.trans e₀ (WeierstrassDilatation.parameterEquiv W₀
  0 (0 * 0) 0 0 c 0 0 c (Eq.symm (zero_mul 0)) rfl rfl rfl)

open WeierstrassModificationX
local notation "B" => MiddleConicOpen W₀ c
local notation "C₀" => ConicCoordinate (WeierstrassCurve.a₁ W₀) c
local notation "h2" => Iff.mpr (residue_eq_zero_iff _) D.a₂_mem
local notation "v" => conicBoundaryUnit W₀ c
local notation "tx" => WeierstrassDilatation.tensorX W (π ^ (k + 1)) b3 b4 b6 K
local notation "ty" => WeierstrassDilatation.tensorY W (π ^ (k + 1)) b3 b4 b6 K

open scoped LaurentPolynomial
local notation "φ" => residueDividedConicMap D k hk b3 b4 b6 h3 h4
local notation "a" => WeierstrassDilatation.residueTangentUnit D
variable (h6 : W.a₆ = (π ^ (k + 1)) ^ 2 * b6)

variable (hp : 2 * (k + 1) < n)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (k + 1) hp b6 h6)
local notation "ha" => D.a₁_unit.map (residue R)
local notation "f₁" => conicBoundaryFirst W₀ c ha hc
local notation "f₂" => conicBoundarySecond W₀ c ha hc
local notation "ψ" => residueNodeConicMap D k hk b3 b4 b6 h3 h4 h6 hp
local notation "L" => K[T;T⁻¹]

/-- The first conic puncture kills the first node coordinate. -/
theorem residueNodeConicFirst_x : f₁ (ψ PolygonNodeLocalization.x) = 0 := by
  rw [residueNodeConicMap_first, map_mul, conicBoundaryFirst_v, mul_zero]

/-- Its opposite node coordinate is the reciprocal of the original conic parameter. -/
theorem residueNodeConicFirst_y : f₁ (ψ PolygonNodeLocalization.y) = LaurentPolynomial.T (-1) := by
  rw [residueNodeConicMap_second, map_mul, map_add, conicBoundaryFirst_v,
    AlgHom.commutes, zero_add]
  exact conicBoundaryFirst_inverse_mul W₀ c ha hc

/-- The second conic puncture keeps the first node coordinate with reciprocal parameter. -/
theorem residueNodeConicSecond_x : f₂ (ψ PolygonNodeLocalization.x) = LaurentPolynomial.T (-1) := by
  rw [residueNodeConicMap_first, map_mul, conicBoundarySecond_v]
  exact conicBoundarySecond_inverse_mul W₀ c ha hc

/-- The second conic puncture kills the opposite node coordinate. -/
theorem residueNodeConicSecond_y : f₂ (ψ PolygonNodeLocalization.y) = 0 := by
  rw [residueNodeConicMap_second, map_mul, map_add, conicBoundarySecond_v, AlgHom.commutes]
  change _ * (-LaurentPolynomial.C (residue R W.a₁) + LaurentPolynomial.C (residue R W.a₁)) = 0
  rw [neg_add_cancel, mul_zero]

/-- The entire first conic map is the second node branch with the parameter inverted. -/
theorem residueNodeConicFirst_eq : (f₁).comp ψ =
    (LaurentPolynomial.invert (R := K)).toAlgHom.comp
      (Polynomial.toLaurentAlg.comp PolygonNodeEqualizer.second) := by
  apply AlgHom.ext_of_adjoin_eq_top PolygonNodePresentation.a_adjoin
  intro z hz
  rcases hz with rfl | hz
  · change f₁ (ψ PolygonNodeLocalization.x) =
      LaurentPolynomial.invert (PolygonNodeLocalization.rightMap PolygonNodeLocalization.x)
    rw [residueNodeConicFirst_x, PolygonNodeLocalization.rightMap_x, map_zero]
  · rcases hz with rfl
    change f₁ (ψ PolygonNodeLocalization.y) =
      LaurentPolynomial.invert (PolygonNodeLocalization.rightMap PolygonNodeLocalization.y)
    rw [residueNodeConicFirst_y, PolygonNodeLocalization.rightMap_y, LaurentPolynomial.invert_T]

/-- The entire second conic map is the first node branch with the parameter inverted. -/
theorem residueNodeConicSecond_eq : (f₂).comp ψ =
    (LaurentPolynomial.invert (R := K)).toAlgHom.comp
      (Polynomial.toLaurentAlg.comp PolygonNodeEqualizer.first) := by
  apply AlgHom.ext_of_adjoin_eq_top PolygonNodePresentation.a_adjoin
  intro z hz
  rcases hz with rfl | hz
  · change f₂ (ψ PolygonNodeLocalization.x) =
      LaurentPolynomial.invert (PolygonNodeLocalization.leftMap PolygonNodeLocalization.x)
    rw [residueNodeConicSecond_x, PolygonNodeLocalization.leftMap_x, LaurentPolynomial.invert_T]
  · rcases hz with rfl
    change f₂ (ψ PolygonNodeLocalization.y) =
      LaurentPolynomial.invert (PolygonNodeLocalization.leftMap PolygonNodeLocalization.y)
    rw [residueNodeConicSecond_y, PolygonNodeLocalization.leftMap_y, map_zero]

open AlgebraicGeometry CategoryTheory
local notation "ι" => Spec.map
  (CommRingCat.ofHom (AlgHom.toRingHom
    (AlgEquiv.toAlgHom (LaurentPolynomial.invert (R := K)))))

/-- The first original conic puncture is exactly the inverted right branch of the node. -/
theorem residueNodeConicFirst_spec :
    Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f₁)) ≫
      Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ)) = ι ≫ PolygonNodeBranches.right K := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (residueNodeConicFirst_eq D k hk b3 b4 b6 h3 h4 h6 hp)

/-- The second original conic puncture is exactly the inverted left branch of the node. -/
theorem residueNodeConicSecond_spec :
    Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f₂)) ≫
      Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ)) = ι ≫ PolygonNodeBranches.left K := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (residueNodeConicSecond_eq D k hk b3 b4 b6 h3 h4 h6 hp)

end FLT.Mazur.WeierstrassSuccessiveX
