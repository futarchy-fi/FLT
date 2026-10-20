/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReciprocalInfinityInput
public import FLT.Mazur.WeierstrassDividedResolvedReciprocal
public import FLT.Mazur.WeierstrassSmoothZeroSection

/-!
# Equal-abscissa pairs lie in the actual resolved reciprocal domain

Given two actual smooth finite-model inputs represented in the divided chart,
their equal-abscissa reciprocal factorization has originally smooth output.
The resulting lift lies in the constructed resolved domain and contracts to
infinity. No factorization through the output open is assumed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation WeierstrassIntegralChart
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "d" => data ⟨j, Nat.lt_succ_of_le hj⟩
local notation "s" => π ^ (start + j)
local notation "H" => WeierstrassDilatation.Coordinate W s (d).b3 (d).b4 (d).b6
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "V" => finiteResolvedReciprocalOutputOpen hπ data j hj

/-- The entire actual equal-abscissa pair factors through the new resolved output domain. -/
theorem finiteResolvedReciprocalInfinity_coverage (a c : H →ₐ[R] S)
    (hu : IsUnit (a (y W s (d).b3 (d).b4 (d).b6) - c (y W s (d).b3 (d).b4 (d).b6)))
    (hx : a (x W s (d).b3 (d).b4 (d).b6) = c (x W s (d).b3 (d).b4 (d).b6))
    (p : Spec (.of S) ⟶ finiteResolvedProduct hπ data j hj)
    (ha : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ finiteSecantDividedChart hπ data j hj =
      p ≫ pullback.fst t t ≫ (U).ι)
    (hc : Spec.map (CommRingCat.ofHom c.toRingHom) ≫ finiteSecantDividedChart hπ data j hj =
      p ≫ pullback.snd t t ≫ (U).ι) :
    ∃ k : Spec (.of S) ⟶ (V).toScheme,
      k ≫ finiteResolvedReciprocalDomainMap hπ data j hj = p ∧
      k ≫ finiteResolvedReciprocalAddition hπ data j hj ≫ (U).ι ≫
          finiteGlobalContraction hπ data j hj =
        Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ integralCurveZero W := by
  let E := dividedPairReciprocalInfinityEvaluation W s (d).b3 (d).b4 (d).b6 a c hu hx
  let e := Spec.map (CommRingCat.ofHom E.toRingHom)
  have he : e ≫ finiteReciprocalInput hπ data j hj =
      p ≫ finiteResolvedPairInclusion hπ data j hj := by
    apply pullback.hom_ext
    · simpa only [e, E, Category.assoc, finiteReciprocalInfinity_fst,
        finiteResolvedPairInclusion, pullback.map, pullback.lift_fst] using ha
    · simpa only [e, E, Category.assoc, finiteReciprocalInfinity_snd,
        finiteResolvedPairInclusion, pullback.map, pullback.lift_snd] using hc
  let l : Spec (.of S) ⟶ finiteResolvedReciprocalSource hπ data j hj :=
    pullback.lift e p he
  have ho : l ≫ finiteResolvedReciprocalOriginalOutput hπ data j hj =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ integralCurveZero W := by
    rw [finiteResolvedReciprocalOriginalOutput, ← Category.assoc]
    change (pullback.lift e p he ≫ pullback.fst _ _) ≫ _ = _
    rw [pullback.lift_fst]
    apply dividedReciprocalSpecialization_toCurve
    change E (algebraMap _ _ (algebraMap _ _
        (dividedPairLeft W s (d).b3 (d).b4 (d).b6 (x W s (d).b3 (d).b4 (d).b6)))) =
      E (algebraMap _ _ (algebraMap _ _
        (dividedPairRight W s (d).b3 (d).b4 (d).b6 (x W s (d).b3 (d).b4 (d).b6))))
    exact (dividedPairReciprocalInfinityEvaluation_left W s (d).b3 (d).b4 (d).b6
      a c hu hx _).trans (hx.trans
        (dividedPairReciprocalInfinityEvaluation_right W s (d).b3 (d).b4 (d).b6
          a c hu hx _).symm)
  have hr : Set.range l ⊆ Set.range (V).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (finiteResolvedReciprocalOriginalOutput hπ data j hj) (l z) ∈ integralSmoothOpen W
    have hz := congrArg (fun f => f z) ho
    rw [Scheme.Hom.comp_apply] at hz
    rw [hz]
    exact integralCurveZero_range_smooth W ⟨_, rfl⟩
  let k := IsOpenImmersion.lift (V).ι l hr
  have hk : k ≫ (V).ι = l := IsOpenImmersion.lift_fac _ _ _
  refine ⟨k, ?_, ?_⟩
  · rw [finiteResolvedReciprocalDomainMap, ← Category.assoc, hk]
    exact pullback.lift_snd _ _ _
  · rw [finiteResolvedReciprocalAddition_contraction, ← Category.assoc, hk, ho]

end FLT.Mazur.WeierstrassDividedDepth
