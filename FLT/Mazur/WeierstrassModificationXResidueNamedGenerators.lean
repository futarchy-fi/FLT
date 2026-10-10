/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXExtendedNormalEvaluation
/-!
# Named generators under the original residue comparison

An opaque package retains the full generic normal equivalence and its equality
proof. It prevents coefficient normalization from unfolding a large cast when
the residue field is substituted. All resulting identities concern the original
coefficient, tensor and chart maps, with the constant coefficient retained.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R) (a : S)
  (hs : algebraMap R S s = 0) (h3 : algebraMap R S b3 = 0)
  (h4 : algebraMap R S b4 = 0)
  (h1 : (W.map (algebraMap R S)).a₁ = a)
  (h2 : (W.map (algebraMap R S)).a₂ = 0)
/-- Seal the constructed equivalence together with its proved equality. -/
opaque extendedNormalSeal :
    {e : ExtendedCoordinate W s b3 b4 b6 S ≃ₐ[S] FiberCoordinate a (algebraMap R S b6) //
      e = extendedNormalEquiv W s b3 b4 b6 a hs h3 h4 h1 h2} :=
  ⟨extendedNormalEquiv W s b3 b4 b6 a hs h3 h4 h1 h2, rfl⟩

/-- The sealed generic normal-form equivalence. -/
def extendedNormalSealedEquiv : ExtendedCoordinate W s b3 b4 b6 S ≃ₐ[S]
    FiberCoordinate a (algebraMap R S b6) :=
  (extendedNormalSeal W s b3 b4 b6 a hs h3 h4 h1 h2).val

/-- The sealed generic map is the original extended normal-form map. -/
theorem extendedNormalSealedEquiv_def :
    extendedNormalSealedEquiv W s b3 b4 b6 a hs h3 h4 h1 h2 =
    extendedNormalEquiv W s b3 b4 b6 a hs h3 h4 h1 h2 :=
  (extendedNormalSeal W s b3 b4 b6 a hs h3 h4 h1 h2).property

/-- The sealed map retains the incidence generator. -/
theorem extendedNormalSealedEquiv_t :
    extendedNormalSealedEquiv W s b3 b4 b6 a hs h3 h4 h1 h2
      (t (W.map (algebraMap R S)) (algebraMap R S s)
        (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6)) =
    fiberT a (algebraMap R S b6) := by
  rw [extendedNormalSealedEquiv_def, extendedNormalEquiv_t]
/-- The sealed map retains the slope generator. -/
theorem extendedNormalSealedEquiv_v :
    extendedNormalSealedEquiv W s b3 b4 b6 a hs h3 h4 h1 h2
      (v (W.map (algebraMap R S)) (algebraMap R S s)
        (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6)) =
    fiberV a (algebraMap R S b6) := by
  rw [extendedNormalSealedEquiv_def, extendedNormalEquiv_v]
end FLT.Mazur.WeierstrassModificationX
namespace FLT.Mazur.WeierstrassModificationX

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * k ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
local notation "K" => ResidueField R
local notation "W'" => W.map (algebraMap R K)
local notation "c" => algebraMap R K b6

/-- Factor the original residue comparison through the generic normal form. -/
theorem residueCoordinateEquiv_eq_extendedNormal :
    residueCoordinateEquiv D k hk0 hk b3 b4 b6 h3 h4 =
    extendedNormalEquiv W (π ^ k) b3 b4 b6 (residue R W.a₁)
      (show algebraMap R K (π ^ k) = 0 from
        WeierstrassDilatation.residue_scale_eq_zero D k hk0)
      (show algebraMap R K b3 = 0 from (residue_eq_zero_iff _).mpr
        (WeierstrassDilatation.divided_linear_mem D k hk b3 b4 h3 h4).1)
      (show algebraMap R K b4 = 0 from (residue_eq_zero_iff _).mpr
        (WeierstrassDilatation.divided_linear_mem D k hk b3 b4 h3 h4).2)
      rfl ((residue_eq_zero_iff _).mpr D.a₂_mem) := rfl

/-- The original residue coefficient map sends incidence to the named fiber generator. -/
theorem residueCoordinateEquiv_t : residueCoordinateEquiv D k hk0 hk b3 b4 b6 h3 h4
    (t W' (algebraMap R K (π ^ k)) (algebraMap R K b3) (algebraMap R K b4) c) =
    fiberT (residue R W.a₁) (residue R b6) := by
  rw [residueCoordinateEquiv_eq_extendedNormal]
  erw [← extendedNormalSealedEquiv_def]
  exact extendedNormalSealedEquiv_t W (π ^ k) b3 b4 b6 (residue R W.a₁) _ _ _ _ _
/-- The original residue coefficient map sends slope to the named fiber generator. -/
theorem residueCoordinateEquiv_v : residueCoordinateEquiv D k hk0 hk b3 b4 b6 h3 h4
    (v W' (algebraMap R K (π ^ k)) (algebraMap R K b3) (algebraMap R K b4) c) =
    fiberV (residue R W.a₁) (residue R b6) := by
  rw [residueCoordinateEquiv_eq_extendedNormal]
  erw [← extendedNormalSealedEquiv_def]
  exact extendedNormalSealedEquiv_v W (π ^ k) b3 b4 b6 (residue R W.a₁) _ _ _ _ _
/-- The actual tensor incidence maps to the named full-fiber incidence. -/
theorem residueFiberEquiv_t : residueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4
    ((1 : K) ⊗ₜ[R] t W (π ^ k) b3 b4 b6) =
    fiberT (residue R W.a₁) (residue R b6) := by
  rw [residueFiberEquiv_t_coordinate, residueCoordinateEquiv_t]

/-- The actual tensor slope maps to the named full-fiber slope. -/
theorem residueFiberEquiv_v : residueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4
    ((1 : K) ⊗ₜ[R] v W (π ^ k) b3 b4 b6) =
    fiberV (residue R W.a₁) (residue R b6) := by
  rw [residueFiberEquiv_v_coordinate, residueCoordinateEquiv_v]

/-- The original chart incidence maps to the named full-fiber incidence. -/
theorem residueNormalMap_t :
    residueNormalMap D k hk0 hk b3 b4 b6 h3 h4 (t W (π ^ k) b3 b4 b6) =
    fiberT (residue R W.a₁) (residue R b6) := by
  rw [residueNormalMap_t_coordinate, residueCoordinateEquiv_t]

/-- The original chart slope maps to the named full-fiber slope. -/
theorem residueNormalMap_v :
    residueNormalMap D k hk0 hk b3 b4 b6 h3 h4 (v W (π ^ k) b3 b4 b6) =
    fiberV (residue R W.a₁) (residue R b6) := by
  rw [residueNormalMap_v_coordinate, residueCoordinateEquiv_v]
end FLT.Mazur.WeierstrassModificationX
