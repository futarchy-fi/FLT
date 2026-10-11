/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationResidueBoundaryFunctions
public import FLT.Mazur.LaurentUnitPoints

/-!
# The original terminal vertical coordinate determines every Laurent point

At equality depth the complete tensor algebra is Laurent, with its original
divided vertical coordinate as parameter. Its character determines the whole point.
-/

@[expose] public noncomputable section
open IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * k ≤ depth) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6) (hp : 2 * k = depth)
local notation "K" => ResidueField R
local notation "A" => ScalarExtension W (π ^ k) b3 b4 b6 K
local notation "e" => residueLaurentEquiv D k hk0 hk b3 b4 b6 h3 h4 h6 hp
variable {C : Type u} [CommRing C] [Algebra (ResidueField R) C]

/-- An actual tensor point of the terminal chart with its original vertical unit. -/
def terminalTensorLaurentPoint (q : Cˣ) : A →ₐ[K] C :=
  (LaurentUnitPoints.evalUnit q).comp (e).toAlgHom

/-- The point's original divided vertical function is its prescribed Laurent unit. -/
theorem terminalTensorLaurentPoint_y (q : Cˣ) :
    terminalTensorLaurentPoint D k hk0 hk b3 b4 b6 h3 h4 h6 hp q
      (tensorY W (π ^ k) b3 b4 b6 K) = q := by
  rw [terminalTensorLaurentPoint, AlgHom.comp_apply]
  change LaurentUnitPoints.evalUnit q (e (tensorY W (π ^ k) b3 b4 b6 K)) = _
  rw [residueLaurentEquiv_y, LaurentUnitPoints.evalUnit_T, zpow_one]

include D hk0 hk h3 h4 h6 hp in
/-- Every original terminal tensor point is determined by its divided vertical coordinate. -/
theorem terminalTensorLaurentPoint_hom_ext (f g : A →ₐ[K] C)
    (hy : f (tensorY W (π ^ k) b3 b4 b6 K) = g (tensorY W (π ^ k) b3 b4 b6 K)) : f = g := by
  have ht : (e).symm (LaurentPolynomial.T 1) = tensorY W (π ^ k) b3 b4 b6 K := by
    apply (e).injective
    rw [AlgEquiv.apply_symm_apply, residueLaurentEquiv_y]
  have he : f.comp (e).symm.toAlgHom = g.comp (e).symm.toAlgHom := by
    apply LaurentUnitPoints.pointsEquiv.injective
    apply Units.ext
    change f ((e).symm (LaurentPolynomial.T 1)) = g ((e).symm (LaurentPolynomial.T 1))
    rw [ht]
    exact hy
  apply AlgHom.ext
  intro t
  have h := congrArg (fun h => h (e t)) he
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] using h

/-- A vertical character comparison identifies the entire terminal output tensor map. -/
theorem terminalTensorLaurentPoint_eq_of_character (f : A →ₐ[K] C) (τ q : Cˣ)
    (hy : f (tensorY W (π ^ k) b3 b4 b6 K) = (τ : C) * q) :
    f = terminalTensorLaurentPoint D k hk0 hk b3 b4 b6 h3 h4 h6 hp (τ * q) := by
  apply terminalTensorLaurentPoint_hom_ext D k hk0 hk b3 b4 b6 h3 h4 h6 hp
  rw [terminalTensorLaurentPoint_y]
  exact hy

end FLT.Mazur.WeierstrassDilatation
