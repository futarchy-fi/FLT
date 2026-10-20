/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPairReciprocalEvaluation
public import FLT.Mazur.WeierstrassDividedFiniteReciprocalInput

/-!
# Actual equal-abscissa pairs in the reciprocal finite-model input open

The constructed algebra factorizations retain both scheme projections into
the same finite model. These identities supply the input compatibility for
the resolved smooth-pair pullback.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
  (hu : IsUnit (a (y W s b3 b4 b6) - c (y W s b3 b4 b6)))
  (hx : a (x W s b3 b4 b6) = c (x W s b3 b4 b6))
local notation "E" => dividedPairReciprocalInfinityEvaluation W s b3 b4 b6 a c hu hx
local notation "H" => Coordinate W s b3 b4 b6
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R H))

/-- The actual first projection of the constructed reciprocal factorization. -/
@[reassoc] theorem dividedPairReciprocalInfinity_fst :
    Spec.map (CommRingCat.ofHom (E).toRingHom) ≫
        dividedPairReciprocalOutputToProduct W s b3 b4 b6 ≫ pullback.fst q q =
      Spec.map (CommRingCat.ofHom a.toRingHom) := by
  rw [dividedPairReciprocalOutputToProduct_fst, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact dividedPairReciprocalInfinityEvaluation_left W s b3 b4 b6 a c hu hx z

/-- The actual second projection of the same reciprocal factorization. -/
@[reassoc] theorem dividedPairReciprocalInfinity_snd :
    Spec.map (CommRingCat.ofHom (E).toRingHom) ≫
        dividedPairReciprocalOutputToProduct W s b3 b4 b6 ≫ pullback.snd q q =
      Spec.map (CommRingCat.ofHom c.toRingHom) := by
  rw [dividedPairReciprocalOutputToProduct_snd, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact dividedPairReciprocalInfinityEvaluation_right W s b3 b4 b6 a c hu hx z

end FLT.Mazur.WeierstrassDilatation

namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [IsDomain R] [IsBezout R] {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  {start n : ℕ} (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j ≤ n)
local notation "d" => data ⟨j, Nat.lt_succ_of_le hj⟩
local notation "s" => π ^ (start + j)
local notation "H" => WeierstrassDilatation.Coordinate W s (d).b3 (d).b4 (d).b6
local notation "base" => finiteGlobalStructure hπ data j hj
variable (a c : WeierstrassDilatation.Coordinate W (π ^ (start + j))
    (data ⟨j, Nat.lt_succ_of_le hj⟩).b3 (data ⟨j, Nat.lt_succ_of_le hj⟩).b4
    (data ⟨j, Nat.lt_succ_of_le hj⟩).b6 →ₐ[R] S)
  (hu : IsUnit (a (y W (π ^ (start + j))
      (data ⟨j, Nat.lt_succ_of_le hj⟩).b3 (data ⟨j, Nat.lt_succ_of_le hj⟩).b4
      (data ⟨j, Nat.lt_succ_of_le hj⟩).b6) - c (y W (π ^ (start + j))
      (data ⟨j, Nat.lt_succ_of_le hj⟩).b3 (data ⟨j, Nat.lt_succ_of_le hj⟩).b4
      (data ⟨j, Nat.lt_succ_of_le hj⟩).b6)))
  (hx : a (x W (π ^ (start + j))
      (data ⟨j, Nat.lt_succ_of_le hj⟩).b3 (data ⟨j, Nat.lt_succ_of_le hj⟩).b4
      (data ⟨j, Nat.lt_succ_of_le hj⟩).b6) = c (x W (π ^ (start + j))
      (data ⟨j, Nat.lt_succ_of_le hj⟩).b3 (data ⟨j, Nat.lt_succ_of_le hj⟩).b4
      (data ⟨j, Nat.lt_succ_of_le hj⟩).b6))
local notation "E" => dividedPairReciprocalInfinityEvaluation W s (d).b3 (d).b4 (d).b6 a c hu hx

/-- The first point retains its exact map into the entire finite model. -/
@[reassoc] theorem finiteReciprocalInfinity_fst :
    Spec.map (CommRingCat.ofHom (E).toRingHom) ≫
        finiteReciprocalInput hπ data j hj ≫ pullback.fst base base =
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ finiteSecantDividedChart hπ data j hj := by
  simp only [finiteReciprocalInput, finiteSecantPairChart, pullback.map, Category.assoc,
    pullback.lift_fst, dividedPairReciprocalInfinity_fst_assoc]

/-- The second point retains its exact map into the same entire finite model. -/
@[reassoc] theorem finiteReciprocalInfinity_snd :
    Spec.map (CommRingCat.ofHom (E).toRingHom) ≫
        finiteReciprocalInput hπ data j hj ≫ pullback.snd base base =
      Spec.map (CommRingCat.ofHom c.toRingHom) ≫ finiteSecantDividedChart hπ data j hj := by
  simp only [finiteReciprocalInput, finiteSecantPairChart, pullback.map, Category.assoc,
    pullback.lift_snd, dividedPairReciprocalInfinity_snd_assoc]

end FLT.Mazur.WeierstrassDividedDepth
