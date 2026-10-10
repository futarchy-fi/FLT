/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXResidueConicBoundaryCoordinates
public import FLT.Mazur.WeierstrassDilatationResidueBoundaryFunctions

/-!
# Oriented terminal parameters on the original conic boundary

The normalized Laurent parameter restricts to v/t. The ordered node
coordinates restrict to v/t and (v+a₁)/t, respectively. These maps are
transported through the actual whole tensor normalization.
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

section Laurent
variable (hp : 2 * (k + 1) = n)
local notation "E" => WeierstrassDilatation.residueLaurentEquiv D (k + 1)
  (Nat.zero_lt_succ k) hk b3 b4 b6 h3 h4 h6 hp

/-- The full normalized Laurent algebra restricts along the original conic boundary. -/
def residueLaurentConicMap : K[T;T⁻¹] →ₐ[K] B :=
  (φ).comp (AlgEquiv.toAlgHom (AlgEquiv.symm E))

/-- The normalized Laurent parameter keeps the original oriented slope ratio. -/
theorem residueLaurentConicMap_parameter :
    residueLaurentConicMap D k hk b3 b4 b6 h3 h4 h6 hp (LaurentPolynomial.T 1) =
      (↑(v)⁻¹ : B) * algebraMap C₀ B (conicV (WeierstrassCurve.a₁ W₀) c) := by
  rw [← WeierstrassDilatation.residueLaurentEquiv_y D (k + 1)
    (Nat.zero_lt_succ k) hk b3 b4 b6 h3 h4 h6 hp]
  change φ ((E).symm ((E) ty)) = _
  rw [AlgEquiv.symm_apply_apply]
  exact residueDividedConicMap_y D k hk b3 b4 b6 h3 h4

end Laurent

section Node
variable (hp : 2 * (k + 1) < n)
local notation "E" => WeierstrassDilatation.residuePolygonEquiv D (k + 1)
  (Nat.zero_lt_succ k) hk b3 b4 b6 h3 h4 h6 hp

/-- The full ordered terminal node algebra restricts along the original conic boundary. -/
def residueNodeConicMap : PolygonNodeEqualizer.A (R := K) →ₐ[K] B :=
  (φ).comp (AlgEquiv.toAlgHom (AlgEquiv.symm E))

/-- The first normalized node coordinate retains v/t, with its original tangent orientation. -/
theorem residueNodeConicMap_first :
    residueNodeConicMap D k hk b3 b4 b6 h3 h4 h6 hp PolygonNodeLocalization.x =
      (↑(v)⁻¹ : B) * algebraMap C₀ B (conicV (WeierstrassCurve.a₁ W₀) c) := by
  rw [← WeierstrassDilatation.residuePolygonEquiv_y D (k + 1)
    (Nat.zero_lt_succ k) hk b3 b4 b6 h3 h4 h6 hp]
  change φ ((E).symm ((E) ty)) = _
  rw [AlgEquiv.symm_apply_apply]
  exact residueDividedConicMap_y D k hk b3 b4 b6 h3 h4

/-- The opposite normalized node coordinate retains (v+a₁)/t, without interchanging branches. -/
theorem residueNodeConicMap_second :
    residueNodeConicMap D k hk b3 b4 b6 h3 h4 h6 hp PolygonNodeLocalization.y =
      (↑(v)⁻¹ : B) * (algebraMap C₀ B (conicV (WeierstrassCurve.a₁ W₀) c) +
        algebraMap K B (residue R W.a₁)) := by
  have H : (E) (ty + algebraMap K T (↑a : K) * tx) = PolygonNodeLocalization.y := by
    rw [map_add, map_mul, AlgEquiv.commutes,
      WeierstrassDilatation.residuePolygonEquiv_y,
      WeierstrassDilatation.residuePolygonEquiv_x,
      ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
    ring
  rw [← H]
  change φ ((E).symm ((E) (ty + algebraMap K T (↑a : K) * tx))) = _
  rw [AlgEquiv.symm_apply_apply, map_add, map_mul, AlgHom.commutes,
    residueDividedConicMap_x, residueDividedConicMap_y,
    WeierstrassDilatation.residueTangentUnit_val]
  ring

end Node

end FLT.Mazur.WeierstrassSuccessiveX
