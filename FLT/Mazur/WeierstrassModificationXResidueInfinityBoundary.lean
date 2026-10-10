/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXResidueNamedGenerators
public import FLT.Mazur.WeierstrassModificationXResidueConicContraction
public import FLT.Mazur.PrincipalOpenTransportGeometry

/-!
# The full original initial infinity boundary in residue normal coordinates

The actual y function becomes the original conic factor times the slope.
The resulting localization comparison retains every original fiber function
and the arbitrary divided constant, before restricting to an exterior component.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * k ≤ depth) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
local notation "K" => ResidueField R
local notation "a" => residue R W.a₁
local notation "c" => residue R b6
local notation "F" => FiberCoordinate a c
local notation "T" => K ⊗[R] Coordinate W (π ^ k) b3 b4 b6
local notation "E" => residueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4
local notation "y₀" => ((1 : K) ⊗ₜ[R] y W (π ^ k) b3 b4 b6 : T)
local notation "q" => fiberConicFactor a c
local notation "v₀" => fiberV a c

/-- The original tensor y is the full conic factor times the original slope. -/
theorem residueInfinityBoundary_y : E y₀ = q * v₀ := by
  change residueNormalMap D k hk0 hk b3 b4 b6 h3 h4 (y W (π ^ k) b3 b4 b6) = _
  rw [residueNormalMap_y, residueNormalMap_x, residueNormalMap_v, residueNormalMap_t,
    IsScalarTower.algebraMap_apply R K F, IsScalarTower.algebraMap_apply R K F]
  rfl

/-- The entire original tensor infinity localization has its exact normalized equation. -/
def residueInfinityBoundaryEquiv :
    Localization.Away y₀ ≃ₐ[K] Localization.Away (q * v₀) :=
  PrincipalOpenTransport.equiv E y₀ (q * v₀)
    (residueInfinityBoundary_y D k hk0 hk b3 b4 b6 h3 h4)

/-- The boundary comparison retains all original tensor restrictions. -/
theorem residueInfinityBoundaryEquiv_base (z : ResidueField R ⊗[R] Coordinate W (π ^ k) b3 b4 b6) :
    residueInfinityBoundaryEquiv D k hk0 hk b3 b4 b6 h3 h4
      (algebraMap T (Localization.Away y₀) z) =
        algebraMap F (Localization.Away (q * v₀)) (E z) :=
  PrincipalOpenTransport.equiv_base _ _ _ _ z

/-- The full original and normalized infinity principal spectra are isomorphic. -/
def residueInfinityBoundaryIso : Spec (.of (Localization.Away (q * v₀))) ≅
    Spec (.of (Localization.Away y₀)) :=
  Scheme.Spec.mapIso
    (residueInfinityBoundaryEquiv D k hk0 hk b3 b4 b6 h3 h4).toRingEquiv.toCommRingCatIso.op

/-- The full normalization preserves the original inclusion on every function. -/
@[reassoc] theorem residueInfinityBoundaryIso_inclusion :
    (residueInfinityBoundaryIso D k hk0 hk b3 b4 b6 h3 h4).hom ≫
      PrincipalOpenTransport.inclusion y₀ =
        PrincipalOpenTransport.inclusion (q * v₀) ≫
          (residueFiberIso D k hk0 hk b3 b4 b6 h3 h4).hom := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext
    (RingHom.ext (residueInfinityBoundaryEquiv_base D k hk0 hk b3 b4 b6 h3 h4))

end FLT.Mazur.WeierstrassModificationX
