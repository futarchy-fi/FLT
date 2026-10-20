/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResolvedTangent
public import FLT.Mazur.WeierstrassDividedSecantOverlapProjections

/-!
# Retained projections on the actual resolved tangent domain

Expose the map to the universal affine tangent and both original input maps.
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
local notation "T" => DividedPairTangentRing W s (d).b3 (d).b4 (d).b6
local notation "a" => dividedPairLeft W s (d).b3 (d).b4 (d).b6
local notation "c" => dividedPairRight W s (d).b3 (d).b4 (d).b6
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "V" => finiteResolvedTangentOutputOpen hπ data j hj

/-- The actual universal affine tangent coordinates of the new multiplication domain. -/
def finiteResolvedTangentProjection : (V).toScheme ⟶ Spec (.of T) :=
  (V).ι ≫ pullback.fst (finiteTangentInput hπ data j hj)
    (finiteResolvedPairInclusion hπ data j hj)

/-- The first full input contracts to the first universal divided input. -/
@[reassoc] theorem finiteResolvedTangentProjection_left :
    finiteResolvedTangentProjection hπ data j hj ≫
        Spec.map (CommRingCat.ofHom ((IsScalarTower.toAlgHom R P T).comp a).toRingHom) ≫
          toCurve d =
      finiteResolvedTangentDomainMap hπ data j hj ≫ pullback.fst t t ≫ (U).ι ≫
        finiteGlobalContraction hπ data j hj := by
  have h := congrArg (fun f => f ≫ pullback.fst base base ≫
      finiteGlobalContraction hπ data j hj)
    (pullback.condition (f := finiteTangentInput hπ data j hj)
      (g := finiteResolvedPairInclusion hπ data j hj))
  simp only [Category.assoc, finiteTangentInput_fst_contraction,
    dividedPairTangentToProduct_fst_assoc, finiteResolvedPairInclusion_fst_assoc] at h
  simpa only [finiteResolvedTangentProjection, finiteResolvedTangentDomainMap,
    finiteResolvedTangentInput, Category.assoc] using congrArg ((V).ι ≫ ·) h

/-- The second full input contracts to the second universal divided input. -/
@[reassoc] theorem finiteResolvedTangentProjection_right :
    finiteResolvedTangentProjection hπ data j hj ≫
        Spec.map (CommRingCat.ofHom ((IsScalarTower.toAlgHom R P T).comp c).toRingHom) ≫
          toCurve d =
      finiteResolvedTangentDomainMap hπ data j hj ≫ pullback.snd t t ≫ (U).ι ≫
        finiteGlobalContraction hπ data j hj := by
  have h := congrArg (fun f => f ≫ pullback.snd base base ≫
      finiteGlobalContraction hπ data j hj)
    (pullback.condition (f := finiteTangentInput hπ data j hj)
      (g := finiteResolvedPairInclusion hπ data j hj))
  simp only [Category.assoc, finiteTangentInput_snd_contraction,
    dividedPairTangentToProduct_snd_assoc, finiteResolvedPairInclusion_snd_assoc] at h
  simpa only [finiteResolvedTangentProjection, finiteResolvedTangentDomainMap,
    finiteResolvedTangentInput, Category.assoc] using congrArg ((V).ι ≫ ·) h

/-- The original output is precisely the universal formula on these affine coordinates. -/
@[reassoc] theorem finiteResolvedTangentProjection_output :
    finiteResolvedTangentProjection hπ data j hj ≫
        dividedTangentToCurve W s (d).b3 (d).b4 (d).b6 a c
          (d).factor3 (d).factor4 (d).factor6 =
      (V).ι ≫ finiteResolvedTangentOriginalOutput hπ data j hj := by
  rfl

/-- The original smooth lift retains that same universal output. -/
@[reassoc] theorem finiteResolvedTangentOriginalSmooth_inclusion :
    finiteResolvedTangentOriginalSmooth hπ data j hj ≫ (integralSmoothOpen W).ι =
      (V).ι ≫ finiteResolvedTangentOriginalOutput hπ data j hj :=
  morphismRestrict_ι _ _

end FLT.Mazur.WeierstrassDividedDepth
