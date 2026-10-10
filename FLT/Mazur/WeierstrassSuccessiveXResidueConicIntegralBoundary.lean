/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXResidueTransitionBaseChange
public import FLT.Mazur.WeierstrassSuccessiveXResidueConicBoundaryGeometry

/-!
# The conic boundary is the original integral tensor transition

The entire conic comparison, composed with the inverse depth transition,
recovers the original conic boundary isomorphism. This identifies scheme
maps before any contraction to the original cubic.
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
local notation "x" => WeierstrassDilatation.x W (π ^ (k + 1)) b3 b4 b6
local notation "t" => coord W (π ^ k) π b3 b4 b6 0
local notation "A" => PrincipalOpenTensor.transitionIso K x t
  (depthOverlapEquiv W π k b3 b4 b6)
local notation "E" => residueConicBoundaryIso D k hk0 hk b3 b4 b6 h3 h4
local notation "c" => residueDividedConicOpenEquiv D k hk b3 b4 b6 h3 h4

/-- The actual conic boundary agrees with the complete integral depth overlap. -/
@[reassoc] theorem residueConicBoundaryIso_integral :
    (E).hom ≫ (A).hom =
      Spec.map (CommRingCat.ofHom (AlgEquiv.toAlgHom c).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change residueMiddleConicOpenEquiv D k hk0 hk b3 b4 b6 h3 h4
    (residueIntegralTransition W π k b3 b4 b6 z) = c z
  rw [← residueMiddleTransition_eq_integral D k hk0 hk b3 b4 b6 h3 h4]
  exact residueMiddleTransition_conic D k hk0 hk b3 b4 b6 h3 h4 z

/-- The inverse integral transition recovers the original full conic boundary isomorphism. -/
@[reassoc] theorem residueDividedConicOpen_spec_boundary :
    Spec.map (CommRingCat.ofHom (AlgEquiv.toAlgHom c).toRingHom) ≫ (A).inv =
      (E).hom := by
  rw [← residueConicBoundaryIso_integral D k hk0 hk b3 b4 b6 h3 h4,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

end FLT.Mazur.WeierstrassSuccessiveX
