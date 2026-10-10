/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXZeroConicIntegralNormalization

/-!
# The zero-stage conic boundary is the original integral transition

Equality on the two original divided tensor coordinates proves equality on
all localized functions. The spectrum equality retains both original maps.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (k : ℕ) (hk0 : k = 0) (hk : 2 * (k + 1) ≤ depth) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
local notation "K" => ResidueField R
local notation "x" => WeierstrassDilatation.x W (π ^ (k + 1)) b3 b4 b6
local notation "t" => coord W (π ^ k) π b3 b4 b6 0
local notation "A" => PrincipalOpenTensor.transitionIso K x t
  (depthOverlapEquiv W π k b3 b4 b6)
local notation "E" => zeroResidueConicBoundaryIso D k hk0 hk b3 b4 b6 h3 h4
local notation "e" => zeroResidueConicOpenEquiv D k hk0 hk b3 b4 b6 h3 h4
local notation "c" => residueDividedConicOpenEquiv D k hk b3 b4 b6 h3 h4
local notation "m" => residueIntegralTransition W π k b3 b4 b6

/-- The whole original integral transition agrees with the zero-stage conic normalization. -/
theorem zeroConicIntegralTransition_eq : (m).trans e = c := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply IsLocalization.algHom_ext
    (Submonoid.powers (WeierstrassDilatation.tensorX W (π ^ (k + 1)) b3 b4 b6 K))
  apply Algebra.TensorProduct.ext_ring
  apply WeierstrassDilatation.hom_ext
  · exact (zeroConicIntegralTransition_x D k hk0 hk b3 b4 b6 h3 h4).trans
      (residueDividedConicMap_x D k hk b3 b4 b6 h3 h4).symm
  · exact (zeroConicIntegralTransition_y D k hk0 hk b3 b4 b6 h3 h4).trans
      (residueDividedConicMap_y D k hk b3 b4 b6 h3 h4).symm

/-- The complete zero-stage conic boundary keeps the actual integral depth transition. -/
@[reassoc] theorem zeroResidueConicBoundaryIso_integral :
    (E).hom ≫ (A).hom =
      Spec.map (CommRingCat.ofHom (AlgEquiv.toAlgHom c).toRingHom) := by
  change (Spec.map _ ≫ Spec.map _) ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change e (m z) = c z
  exact DFunLike.congr_fun (zeroConicIntegralTransition_eq D k hk0 hk b3 b4 b6 h3 h4) z

/-- The inverse original transition recovers the entire zero-stage conic boundary. -/
@[reassoc] theorem zeroResidueDividedConicOpen_spec_boundary :
    Spec.map (CommRingCat.ofHom (AlgEquiv.toAlgHom c).toRingHom) ≫ (A).inv =
      (E).hom := by
  rw [← zeroResidueConicBoundaryIso_integral D k hk0 hk b3 b4 b6 h3 h4,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

end FLT.Mazur.WeierstrassSuccessiveX
