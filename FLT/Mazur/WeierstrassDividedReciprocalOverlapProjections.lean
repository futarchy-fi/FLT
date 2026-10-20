/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResolvedReciprocal
public import FLT.Mazur.WeierstrassDividedSecantOverlapProjections

/-!
# Retained projections on the actual resolved reciprocal domain

Expose the map to the universal affine reciprocal and both original input maps.
These identities allow overlap comparisons without unfolding tensor products
or replacing either resolved input by its contraction.
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
local notation "T" => DividedPairReciprocalOutputRing W s (d).b3 (d).b4 (d).b6
local notation "Q" => DividedPairReciprocalRing W s (d).b3 (d).b4 (d).b6
local notation "e" => (IsScalarTower.toAlgHom R Q T).comp (IsScalarTower.toAlgHom R P Q)
local notation "a" => dividedPairLeft W s (d).b3 (d).b4 (d).b6
local notation "c" => dividedPairRight W s (d).b3 (d).b4 (d).b6
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "V" => finiteResolvedReciprocalOutputOpen hπ data j hj

/-- The actual universal affine reciprocal coordinates of the new multiplication domain. -/
def finiteResolvedReciprocalProjection : (V).toScheme ⟶ Spec (.of T) :=
  (V).ι ≫ pullback.fst (finiteReciprocalInput hπ data j hj)
    (finiteResolvedPairInclusion hπ data j hj)

/-- The first full input contracts to the first universal divided input. -/
@[reassoc] theorem finiteResolvedReciprocalProjection_left :
    finiteResolvedReciprocalProjection hπ data j hj ≫
        Spec.map (CommRingCat.ofHom ((e).comp a).toRingHom) ≫
          toCurve d =
      finiteResolvedReciprocalDomainMap hπ data j hj ≫ pullback.fst t t ≫ (U).ι ≫
        finiteGlobalContraction hπ data j hj := by
  have h := congrArg (fun f => f ≫ pullback.fst base base ≫
      finiteGlobalContraction hπ data j hj)
    (pullback.condition (f := finiteReciprocalInput hπ data j hj)
      (g := finiteResolvedPairInclusion hπ data j hj))
  simp only [Category.assoc, finiteReciprocalInput_fst_contraction,
    dividedPairReciprocalOutputToProduct_fst_assoc, finiteResolvedPairInclusion_fst_assoc] at h
  simpa only [finiteResolvedReciprocalProjection, finiteResolvedReciprocalDomainMap,
    finiteResolvedReciprocalInput, Category.assoc, AlgHom.comp_assoc] using congrArg ((V).ι ≫ ·) h

/-- The second full input contracts to the second universal divided input. -/
@[reassoc] theorem finiteResolvedReciprocalProjection_right :
    finiteResolvedReciprocalProjection hπ data j hj ≫
        Spec.map (CommRingCat.ofHom ((e).comp c).toRingHom) ≫
          toCurve d =
      finiteResolvedReciprocalDomainMap hπ data j hj ≫ pullback.snd t t ≫ (U).ι ≫
        finiteGlobalContraction hπ data j hj := by
  have h := congrArg (fun f => f ≫ pullback.snd base base ≫
      finiteGlobalContraction hπ data j hj)
    (pullback.condition (f := finiteReciprocalInput hπ data j hj)
      (g := finiteResolvedPairInclusion hπ data j hj))
  simp only [Category.assoc, finiteReciprocalInput_snd_contraction,
    dividedPairReciprocalOutputToProduct_snd_assoc, finiteResolvedPairInclusion_snd_assoc] at h
  simpa only [finiteResolvedReciprocalProjection, finiteResolvedReciprocalDomainMap,
    finiteResolvedReciprocalInput, Category.assoc, AlgHom.comp_assoc] using congrArg ((V).ι ≫ ·) h

/-- The original output is precisely the universal formula on these affine coordinates. -/
@[reassoc] theorem finiteResolvedReciprocalProjection_output :
    finiteResolvedReciprocalProjection hπ data j hj ≫
        dividedReciprocalToCurve W s (d).b3 (d).b4 (d).b6 a c
          (d).factor3 (d).factor4 (d).factor6 =
      (V).ι ≫ finiteResolvedReciprocalOriginalOutput hπ data j hj := by
  rfl

/-- The original smooth lift retains that same universal output. -/
@[reassoc] theorem finiteResolvedReciprocalOriginalSmooth_inclusion :
    finiteResolvedReciprocalOriginalSmooth hπ data j hj ≫ (integralSmoothOpen W).ι =
      (V).ι ≫ finiteResolvedReciprocalOriginalOutput hπ data j hj :=
  morphismRestrict_ι _ _

end FLT.Mazur.WeierstrassDividedDepth
