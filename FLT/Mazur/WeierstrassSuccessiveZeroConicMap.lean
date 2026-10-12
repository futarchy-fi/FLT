/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXZeroConicBoundary
public import FLT.Mazur.WeierstrassSmoothSuccessiveTensorInput

/-!
# Original tensor functions on the first retained scale-one conic

The complete conic restriction keeps incidence, slope and horizontal
coordinates. It is the algebra map of the already constructed geometric immersion.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {k depth : ℕ}
  (D : SplitNodeDepth W π depth) (hk0 : k = 0) (hk : 2 * (k + 1) ≤ depth)
  (d : WeierstrassDividedDepth.Data W π (k + 1))
local notation "K" => ResidueField R
local notation "a" => residue R W.a₁
local notation "c" => residue R d.b6
local notation "T" => ScalarExtension W (π ^ k) π d.b3 d.b4 d.b6 K
local notation "E" => zeroResidueFiberEquiv D k hk0 hk d.b3 d.b4 d.b6 d.factor3 d.factor4

/-- Restriction of the full original tensor algebra to its actual scale-one conic. -/
def zeroResidueConicMap : T →ₐ[K] ConicCoordinate a c :=
  (fiberConicMap a c).comp (E).toAlgHom

/-- Original incidence is the full conic incidence coordinate. -/
theorem zeroResidueConicMap_t :
    zeroResidueConicMap D hk0 hk d (tensorCoord W (π ^ k) π d.b3 d.b4 d.b6 K 0) =
      conicT a c := by
  change fiberConicMap a c (E _) = _
  rw [zeroResidueFiberEquiv_t, fiberConicMap_t]

/-- Original slope retains the chosen zero-root ordering. -/
theorem zeroResidueConicMap_v :
    zeroResidueConicMap D hk0 hk d (tensorCoord W (π ^ k) π d.b3 d.b4 d.b6 K 1) =
      conicV a c := by
  change fiberConicMap a c (E _) = _
  rw [zeroResidueFiberEquiv_v, fiberConicMap_v]

/-- The original horizontal coordinate vanishes on the entire scale-one conic. -/
theorem zeroResidueConicMap_u :
    zeroResidueConicMap D hk0 hk d (tensorCoord W (π ^ k) π d.b3 d.b4 d.b6 K 2) = 0 := by
  change fiberConicMap a c (E _) = _
  rw [zeroResidueFiberEquiv_u, map_sub, map_mul, map_add, map_mul, map_pow,
    fiberConicMap_v, fiberConicMap_t, AlgHom.commutes, AlgHom.commutes]
  have h := conic_relation a c
  linear_combination h

/-- The entire algebra restriction is the independently constructed conic immersion. -/
theorem zeroResidueConicMap_spec :
    Spec.map (CommRingCat.ofHom (zeroResidueConicMap D hk0 hk d).toRingHom) =
      zeroResidueConicImmersion D k hk0 hk d.b3 d.b4 d.b6 d.factor3 d.factor4 := by
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassSuccessiveX
