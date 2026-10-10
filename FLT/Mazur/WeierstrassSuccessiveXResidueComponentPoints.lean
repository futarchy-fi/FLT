/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXResidueIncidencePoints
public import FLT.Mazur.WeierstrassSuccessiveXResidueMiddleContraction
public import FLT.Mazur.WeierstrassModificationXConicIncidenceOrientation

/-!
# The ordered middle sections on the full conic and lines

The two conic markings and the origins of the ordered horizontal lines give
exactly the previously constructed tensor incidence points.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory Polynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
local notation "K" => ResidueField R
local notation "T" => WeierstrassSuccessiveX.ScalarExtension W (π ^ k) π b3 b4 b6 K
local notation "a" => residue R W.a₁
local notation "c" => residue R b6
local notation "ha" => D.a₁_unit.map (residue R)
local notation "first" => residueFirstIncidencePoint D k hk0 hk b3 b4 b6 h3 h4
local notation "second" => residueSecondIncidencePoint D k hk0 hk b3 b4 b6 h3 h4
local notation "C" => residueSuccessiveConicMap D k hk0 hk b3 b4 b6 h3 h4
local notation "L" => residueSuccessiveLineMap D k hk0 hk b3 b4 b6 h3 h4
local notation "W₀" => W.map (residue R)

/-- The original first conic marking is the first middle-node tensor point. -/
theorem residueFirstIncidencePoint_conic :
    (conicFirstIncidencePoint a c ha).comp C = first := by
  apply Algebra.TensorProduct.ext_ring
  apply WeierstrassSuccessiveX.hom_ext
  intro i
  change conicFirstIncidencePoint a c ha
    (C (tensorCoord W (π ^ k) π b3 b4 b6 K i)) =
      first (tensorCoord W (π ^ k) π b3 b4 b6 K i)
  rw [residueSuccessiveConicMap_coord, residueFirstIncidencePoint_coord]
  fin_cases i
  · exact conicFirstIncidencePoint_t a c ha
  · exact conicFirstIncidencePoint_v a c ha
  · exact map_zero _

/-- The opposite original conic marking is the second middle-node tensor point. -/
theorem residueSecondIncidencePoint_conic :
    (conicSecondIncidencePoint a c ha).comp C = second := by
  apply Algebra.TensorProduct.ext_ring
  apply WeierstrassSuccessiveX.hom_ext
  intro i
  change conicSecondIncidencePoint a c ha
    (C (tensorCoord W (π ^ k) π b3 b4 b6 K i)) =
      second (tensorCoord W (π ^ k) π b3 b4 b6 K i)
  rw [residueSuccessiveConicMap_coord, residueSecondIncidencePoint_coord]
  fin_cases i
  · exact conicSecondIncidencePoint_t a c ha
  · exact conicSecondIncidencePoint_v a c ha
  · exact map_zero _

/-- The zero-slope horizontal line meets the conic at the first tensor point. -/
theorem residueFirstIncidencePoint_line :
    (aeval (0 : K)).comp (L 0 (middle_first_root W₀)) = first := by
  apply Algebra.TensorProduct.ext_ring
  apply WeierstrassSuccessiveX.hom_ext
  intro i
  change aeval (0 : K)
    (L 0 (middle_first_root W₀) (tensorCoord W (π ^ k) π b3 b4 b6 K i)) =
      first (tensorCoord W (π ^ k) π b3 b4 b6 K i)
  rw [residueSuccessiveLineMap_coord, residueFirstIncidencePoint_coord]
  fin_cases i
  · exact map_zero _
  · exact aeval_C _ _
  · exact aeval_X _

/-- The opposite horizontal line meets the conic at the second tensor point. -/
theorem residueSecondIncidencePoint_line :
    (aeval (0 : K)).comp (L (-a) (middle_second_root W₀)) = second := by
  apply Algebra.TensorProduct.ext_ring
  apply WeierstrassSuccessiveX.hom_ext
  intro i
  change aeval (0 : K)
    (L (-a) (middle_second_root W₀) (tensorCoord W (π ^ k) π b3 b4 b6 K i)) =
      second (tensorCoord W (π ^ k) π b3 b4 b6 K i)
  rw [residueSuccessiveLineMap_coord, residueSecondIncidencePoint_coord]
  fin_cases i
  · exact map_zero _
  · exact aeval_C _ _
  · exact aeval_X _

/-- The actual conic immersion is induced by the named map on tensor functions. -/
theorem residueSuccessiveConicImmersion_eq_spec :
    residueSuccessiveConicImmersion D k hk0 hk b3 b4 b6 h3 h4 =
      Spec.map (CommRingCat.ofHom (AlgHom.toRingHom C)) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

/-- The actual ordered line immersion is induced by its original tensor function map. -/
theorem residueSuccessiveLineImmersion_eq_spec (r : K)
    (hr : r * (r + a) = 0) :
    residueSuccessiveLineImmersion D k hk0 hk b3 b4 b6 h3 h4 r hr =
      Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (L r hr))) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassSuccessiveX
