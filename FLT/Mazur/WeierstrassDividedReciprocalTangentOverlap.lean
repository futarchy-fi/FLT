/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReciprocalTangentScheme
public import FLT.Mazur.WeierstrassDividedReciprocalOverlapProjections
public import FLT.Mazur.WeierstrassDividedTangentOverlapProjections
public import FLT.Mazur.WeierstrassDividedGlobalFiniteSmoothActionUnique

/-!
# The actual resolved reciprocal and tangent lifts agree on their overlap

Equality of maps into the full resolved product retains both divided inputs.
The formulas agree before resolution; originally smooth output uniqueness
then identifies their actual lifts into the same finite model.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "d" => data ⟨j, Nat.lt_succ_of_le hj⟩
local notation "s" => π ^ (start + j)
local notation "P" => DividedPairRing W s (d).b3 (d).b4 (d).b6
local notation "Q" => DividedPairReciprocalRing W s (d).b3 (d).b4 (d).b6
local notation "T" => DividedPairReciprocalOutputRing W s (d).b3 (d).b4 (d).b6
local notation "a" => dividedPairLeft W s (d).b3 (d).b4 (d).b6
local notation "c" => dividedPairRight W s (d).b3 (d).b4 (d).b6
local notation "U" => (finiteGlobalStructure hπ data j hj).smoothLocus
local notation "Vt" => finiteResolvedReciprocalOutputOpen hπ data j hj
local notation "Vs" => finiteResolvedTangentOutputOpen hπ data j hj

variable {X : Scheme.{u}}
  (p : X ⟶ (finiteResolvedReciprocalOutputOpen hπ data j hj).toScheme)
  (q : X ⟶ (finiteResolvedTangentOutputOpen hπ data j hj).toScheme)
  (hpq : p ≫ finiteResolvedReciprocalDomainMap hπ data j hj =
    q ≫ finiteResolvedTangentDomainMap hπ data j hj)

include hpq in
/-- The original formulas agree on the actual overlap inside the full resolved product. -/
theorem finiteResolvedReciprocal_tangentOriginal :
    p ≫ (Vt).ι ≫ finiteResolvedReciprocalOriginalOutput hπ data j hj =
      q ≫ (Vs).ι ≫ finiteResolvedTangentOriginalOutput hπ data j hj := by
  have ht : finiteResolvedReciprocalProjection hπ data j hj ≫ finiteReciprocalInput hπ data j hj =
      finiteResolvedReciprocalDomainMap hπ data j hj ≫
        finiteResolvedPairInclusion hπ data j hj := by
    simp only [finiteResolvedReciprocalProjection, finiteResolvedReciprocalDomainMap,
      finiteResolvedReciprocalInput, Category.assoc, pullback.condition]
  have hs : finiteResolvedTangentProjection hπ data j hj ≫ finiteTangentInput hπ data j hj =
      finiteResolvedTangentDomainMap hπ data j hj ≫
        finiteResolvedPairInclusion hπ data j hj := by
    simp only [finiteResolvedTangentProjection, finiteResolvedTangentDomainMap,
      finiteResolvedTangentInput, Category.assoc, pullback.condition]
  have he : (p ≫ finiteResolvedReciprocalProjection hπ data j hj) ≫
      (dividedPairReciprocalOutputInclusion W s (d).b3 (d).b4 (d).b6 ≫
        dividedPairReciprocalInclusion W s (d).b3 (d).b4 (d).b6) =
        (q ≫ finiteResolvedTangentProjection hπ data j hj) ≫
          dividedPairTangentInclusion W s (d).b3 (d).b4 (d).b6 := by
    apply (cancel_mono (dividedPairSpecIso W s (d).b3 (d).b4 (d).b6).inv).mp
    apply (cancel_mono (finiteSecantPairChart hπ data j hj)).mp
    have h := congrArg (· ≫ finiteResolvedPairInclusion hπ data j hj) hpq
    rw [Category.assoc, Category.assoc, ← ht, ← hs] at h
    simpa only [finiteReciprocalInput, finiteTangentInput, 
      dividedPairReciprocalOutputToProduct, dividedPairReciprocalToProduct,
      dividedPairTangentToProduct, Category.assoc] using h
  have he' : (p ≫ finiteResolvedReciprocalProjection hπ data j hj) ≫
      Spec.map (CommRingCat.ofHom
        (((IsScalarTower.toAlgHom R Q T).comp
          (IsScalarTower.toAlgHom R P Q)).toRingHom)) =
        (q ≫ finiteResolvedTangentProjection hπ data j hj) ≫
          dividedPairTangentInclusion W s (d).b3 (d).b4 (d).b6 := by
    have hi : dividedPairReciprocalOutputInclusion W s (d).b3 (d).b4 (d).b6 ≫
        dividedPairReciprocalInclusion W s (d).b3 (d).b4 (d).b6 =
          Spec.map (CommRingCat.ofHom
            (((IsScalarTower.toAlgHom R Q T).comp
              (IsScalarTower.toAlgHom R P Q)).toRingHom)) := by
      rw [dividedPairReciprocalOutputInclusion, dividedPairReciprocalInclusion,
        ← Spec.map_comp]
      apply congrArg Spec.map
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro z
      rfl
    rw [hi] at he
    exact he
  have h := dividedReciprocalTangent_scheme W s (d).b3 (d).b4 (d).b6 a c
    (d).factor3 (d).factor4 (d).factor6
    (p ≫ finiteResolvedReciprocalProjection hπ data j hj)
    (q ≫ finiteResolvedTangentProjection hπ data j hj) he'
  simpa only [Category.assoc, finiteResolvedReciprocalProjection_output,
    finiteResolvedTangentProjection_output] using h

include hpq in
/-- Equality of actual resolved lifts uses only uniqueness above an originally smooth output. -/
theorem finiteResolvedReciprocal_tangentOverlap :
    p ≫ finiteResolvedReciprocalAddition hπ data j hj =
      q ≫ finiteResolvedTangentAddition hπ data j hj := by
  apply (cancel_mono (U).ι).mp
  apply finiteGlobal_smooth_output_hom_ext hπ data j hj
    (p ≫ finiteResolvedReciprocalOriginalSmooth hπ data j hj)
  · simp only [Category.assoc, finiteResolvedReciprocalAddition_contraction,
      finiteResolvedReciprocalOriginalSmooth_inclusion]
  · simp only [Category.assoc, finiteResolvedTangentAddition_contraction,
      finiteResolvedReciprocalOriginalSmooth_inclusion]
    exact (finiteResolvedReciprocal_tangentOriginal hπ data j hj p q hpq).symm

end FLT.Mazur.WeierstrassDividedDepth
