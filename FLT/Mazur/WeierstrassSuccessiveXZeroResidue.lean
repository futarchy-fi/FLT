/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXScaleOne
public import FLT.Mazur.WeierstrassSuccessiveXResidueMiddle
public import FLT.Mazur.WeierstrassModificationXFiberNormalForm

/-!
# The full first successive residue chart at preceding depth zero

The preceding scale is one. The full tensor chart is the original horizontal
fiber t*(v*(v+a)-c*t²)=0, keeping the divided constant c even at middle depth.
All three successive functions survive, with u=v*(v+a)-c*t².
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (k : ℕ) (hk0 : k = 0) (hk : 2 * (k + 1) ≤ depth) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
local notation "K" => ResidueField R
local notation "W₀" => W.map (residue R)
local notation "a" => residue R W.a₁
local notation "c" => residue R b6
open WeierstrassModificationX
local notation "F" => FiberCoordinate a c
local notation "t" => fiberT a c
local notation "v" => fiberV a c

/-- At preceding depth zero the full specialized chart keeps scale one and the divided constant. -/
def zeroResidueRetainedEquiv : ExtendedCoordinate W (π ^ k) π b3 b4 b6 K ≃ₐ[K]
    Coordinate W₀ 1 0 0 0 c := by
  obtain ⟨hb3, hb4⟩ := WeierstrassDilatation.divided_linear_mem D (k + 1) hk b3 b4 h3 h4
  apply parameterEquiv _ _ _ _ _ _ _ _ _ _ _
  · simp only [hk0, pow_zero, map_one]
  · exact (residue_eq_zero_iff _).mpr
      (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
  · exact (residue_eq_zero_iff _).mpr hb3
  · exact (residue_eq_zero_iff _).mpr hb4
  · rfl

/-- All original specialized coordinates survive the scale-one normalization. -/
theorem zeroResidueRetainedEquiv_coord (i : Fin 3) :
    zeroResidueRetainedEquiv D k hk0 hk b3 b4 b6 h3 h4
      (extendedCoord W (π ^ k) π b3 b4 b6 K i) = coord W₀ 1 0 0 0 c i :=
  parameterEquiv_coord _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl i

/-- The actual tensor fiber is the entire horizontal equation, with no components discarded. -/
def zeroResidueFiberEquiv : ScalarExtension W (π ^ k) π b3 b4 b6 K ≃ₐ[K] F :=
  (baseChangeEquiv W (π ^ k) π b3 b4 b6 K).trans
    ((zeroResidueRetainedEquiv D k hk0 hk b3 b4 b6 h3 h4).trans
      ((scaleOneModificationEquiv W₀ 0 0 0 c).trans
        (fiberNormalEquiv a c W₀ rfl ((residue_eq_zero_iff _).mpr D.a₂_mem))))

/-- The original incidence ratio is retained on the entire first successive fiber. -/
theorem zeroResidueFiberEquiv_t :
    zeroResidueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4
      (tensorCoord W (π ^ k) π b3 b4 b6 K 0) = t := by
  simp only [zeroResidueFiberEquiv, AlgEquiv.trans_apply, baseChangeEquiv_coord,
    zeroResidueRetainedEquiv_coord, scaleOneModificationEquiv_coord,
    Matrix.cons_val_zero, fiberNormalEquiv_t]

/-- The original tangent slope is retained on all components of the first successive fiber. -/
theorem zeroResidueFiberEquiv_v :
    zeroResidueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4
      (tensorCoord W (π ^ k) π b3 b4 b6 K 1) = v := by
  rw [zeroResidueFiberEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    baseChangeEquiv_coord, zeroResidueRetainedEquiv_coord, scaleOneModificationEquiv_coord]
  exact fiberNormalEquiv_v a c W₀ rfl ((residue_eq_zero_iff _).mpr D.a₂_mem)

/-- The original horizontal coordinate keeps its full quadratic and divided-constant expression. -/
theorem zeroResidueFiberEquiv_u :
    zeroResidueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4
      (tensorCoord W (π ^ k) π b3 b4 b6 K 2) =
        v * (v + algebraMap K F a) - algebraMap K F c * t ^ 2 := by
  rw [zeroResidueFiberEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    baseChangeEquiv_coord, zeroResidueRetainedEquiv_coord, scaleOneModificationEquiv_coord]
  change fiberNormalEquiv a c W₀ rfl ((residue_eq_zero_iff _).mpr D.a₂_mem)
    (WeierstrassModificationX.x W₀ 0 0 0 c) = _
  simp only [WeierstrassModificationX.x, map_sub, map_add, map_mul, map_pow,
    AlgEquiv.commutes, fiberNormalEquiv_t, fiberNormalEquiv_v, map_zero, zero_mul, add_zero]
  have h2 : (W₀).a₂ = 0 := (residue_eq_zero_iff _).mpr D.a₂_mem
  rw [h2, map_zero, zero_add]
  change v ^ 2 + algebraMap K F a * v - algebraMap K F c * t ^ 2 = _
  ring

end FLT.Mazur.WeierstrassSuccessiveX
