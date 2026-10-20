/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedCrossDepthReciprocalSecantScheme
public import FLT.Mazur.WeierstrassDividedReciprocalOverlapProjections
public import FLT.Mazur.WeierstrassDividedSecantFlatSourceExt
public import FLT.Mazur.WeierstrassDividedGlobalFiniteSmoothActionUnique

/-!
# Resolved reciprocal comparison with a secant at an independent input depth

The resolved-product projections retain original cubic inputs. These equalities
identify the actual reciprocal output with a supplied secant formula even
when the secant input depth differs from the reciprocal chart depth.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation WeierstrassIntegralChart
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n k : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "d₀" => data ⟨j, Nat.lt_succ_of_le hj⟩
local notation "s₀" => π ^ (start + j)
local notation "P" => DividedPairRing W s₀ (d₀).b3 (d₀).b4 (d₀).b6
local notation "Q" => DividedPairReciprocalRing W s₀ (d₀).b3 (d₀).b4 (d₀).b6
local notation "O" => DividedPairReciprocalOutputRing W s₀ (d₀).b3 (d₀).b4 (d₀).b6
local notation "a₀" => dividedPairLeft W s₀ (d₀).b3 (d₀).b4 (d₀).b6
local notation "c₀" => dividedPairRight W s₀ (d₀).b3 (d₀).b4 (d₀).b6
local notation "e₀" => (IsScalarTower.toAlgHom R Q O).comp (IsScalarTower.toAlgHom R P Q)
local notation "T" => DividedSecantRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "e" => IsScalarTower.toAlgHom R S T
local notation "U" => (finiteGlobalStructure hπ data j hj).smoothLocus
local notation "t" => (U).ι ≫ finiteGlobalStructure hπ data j hj
local notation "V" => finiteResolvedReciprocalOutputOpen hπ data j hj
local notation "tan" => dividedSecantToCurve W (π ^ k) d.b3 d.b4 d.b6 a c
  d.factor3 d.factor4 d.factor6

/-- Matching original inputs compare the old reciprocal law with any flat secant refinement. -/
theorem finiteResolvedReciprocal_crossDepthSecantOriginal {X : Scheme.{u}}
    (p : X ⟶ (V).toScheme) (q : X ⟶ Spec (.of T)) [Flat q]
    (ha : p ≫ finiteResolvedReciprocalDomainMap hπ data j hj ≫ pullback.fst t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      q ≫ Spec.map (CommRingCat.ofHom ((e).comp a).toRingHom) ≫ toCurve d)
    (hc : p ≫ finiteResolvedReciprocalDomainMap hπ data j hj ≫ pullback.snd t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      q ≫ Spec.map (CommRingCat.ofHom ((e).comp c).toRingHom) ≫ toCurve d) :
    p ≫ (V).ι ≫ finiteResolvedReciprocalOriginalOutput hπ data j hj = q ≫ tan := by
  let f := p ≫ finiteResolvedReciprocalProjection hπ data j hj
  have hl : f ≫ Spec.map (CommRingCat.ofHom ((e₀).comp a₀).toRingHom) ≫ toCurve d₀ =
      q ≫ Spec.map (CommRingCat.ofHom ((e).comp a).toRingHom) ≫ toCurve d := by
    dsimp only [f]
    rw [Category.assoc, finiteResolvedReciprocalProjection_left]
    exact ha
  have hr : f ≫ Spec.map (CommRingCat.ofHom ((e₀).comp c₀).toRingHom) ≫ toCurve d₀ =
      q ≫ Spec.map (CommRingCat.ofHom ((e).comp c).toRingHom) ≫ toCurve d := by
    dsimp only [f]
    rw [Category.assoc, finiteResolvedReciprocalProjection_right]
    exact hc
  let b := q ≫ Spec.map (CommRingCat.ofHom (algebraMap R T))
  let _ : Flat (Spec.map (CommRingCat.ofHom (algebraMap R T))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let _ : Flat b := inferInstanceAs (Flat (q ≫ _))
  have hb : f ≫ Spec.map (CommRingCat.ofHom (algebraMap R O)) = b := by
    simpa only [Category.assoc, toCurve_structure, specAlgHom_structure] using
      congrArg (· ≫ integralCurveStructure W) hl
  have h := dividedCrossDepthReciprocalSecant_scheme
    W s₀ (d₀).b3 (d₀).b4 (d₀).b6 (π ^ k) d.b3 d.b4 d.b6 a₀ c₀ a c
    (d₀).factor3 (d₀).factor4 (d₀).factor6 d.factor3 d.factor4 d.factor6
    b (IsRegular.of_ne_zero (pow_ne_zero _ hπ)) f q hb rfl
    (by simpa only [toCurve, WeierstrassDilatation.toCurve,
          AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp,
          Spec.map_comp, Category.assoc] using hl)
    (by simpa only [toCurve, WeierstrassDilatation.toCurve,
          AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp,
          Spec.map_comp, Category.assoc] using hr)
  simpa only [f, Category.assoc, finiteResolvedReciprocalProjection_output] using h

/-- Every actual finite-model secant lift equals the old reciprocal output on this overlap. -/
theorem finiteResolvedReciprocal_crossDepthSecantOverlap {X : Scheme.{u}}
    (p : X ⟶ (V).toScheme) (q : X ⟶ Spec (.of T)) [Flat q]
    (ha : p ≫ finiteResolvedReciprocalDomainMap hπ data j hj ≫ pullback.fst t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      q ≫ Spec.map (CommRingCat.ofHom ((e).comp a).toRingHom) ≫ toCurve d)
    (hc : p ≫ finiteResolvedReciprocalDomainMap hπ data j hj ≫ pullback.snd t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      q ≫ Spec.map (CommRingCat.ofHom ((e).comp c).toRingHom) ≫ toCurve d)
    (z : X ⟶ (U).toScheme)
    (hz : z ≫ (U).ι ≫ finiteGlobalContraction hπ data j hj = q ≫ tan) :
    p ≫ finiteResolvedReciprocalAddition hπ data j hj = z := by
  apply (cancel_mono (U).ι).mp
  apply finiteGlobal_smooth_output_hom_ext hπ data j hj
    (p ≫ finiteResolvedReciprocalOriginalSmooth hπ data j hj)
  · simp only [Category.assoc, finiteResolvedReciprocalAddition_contraction,
      finiteResolvedReciprocalOriginalSmooth_inclusion]
  · rw [Category.assoc, hz]
    simpa only [Category.assoc, finiteResolvedReciprocalOriginalSmooth_inclusion] using
      (finiteResolvedReciprocal_crossDepthSecantOriginal hπ data j hj d a c p q ha hc).symm

end FLT.Mazur.WeierstrassDividedDepth
