/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedCrossDepthTangentSecantScheme
public import FLT.Mazur.WeierstrassDividedSecantOverlapProjections
public import FLT.Mazur.WeierstrassDividedTangentFlatSourceExt
public import FLT.Mazur.WeierstrassDividedGlobalFiniteSmoothActionUnique

/-!
# Resolved secant comparison with a tangent at an independent input depth

The resolved-product projections retain original cubic inputs. These equalities
identify the actual secant output with a supplied tangent formula even
when the tangent input depth differs from the secant chart depth.
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
local notation "Q" => DividedPairSecantRing W s₀ (d₀).b3 (d₀).b4 (d₀).b6
local notation "a₀" => dividedPairLeft W s₀ (d₀).b3 (d₀).b4 (d₀).b6
local notation "c₀" => dividedPairRight W s₀ (d₀).b3 (d₀).b4 (d₀).b6
local notation "e₀" => IsScalarTower.toAlgHom R P Q
local notation "T" => DividedTangentRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "e" => IsScalarTower.toAlgHom R S T
local notation "U" => (finiteGlobalStructure hπ data j hj).smoothLocus
local notation "t" => (U).ι ≫ finiteGlobalStructure hπ data j hj
local notation "V" => finiteResolvedSecantOutputOpen hπ data j hj
local notation "tan" => dividedTangentToCurve W (π ^ k) d.b3 d.b4 d.b6 a c
  d.factor3 d.factor4 d.factor6

/-- Matching original inputs compare the old secant law with any flat tangent refinement. -/
theorem finiteResolvedSecant_crossDepthTangentOriginal {X : Scheme.{u}}
    (p : X ⟶ (V).toScheme) (q : X ⟶ Spec (.of T)) [Flat q]
    (ha : p ≫ finiteResolvedSecantDomainMap hπ data j hj ≫ pullback.fst t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      q ≫ Spec.map (CommRingCat.ofHom ((e).comp a).toRingHom) ≫ toCurve d)
    (hc : p ≫ finiteResolvedSecantDomainMap hπ data j hj ≫ pullback.snd t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      q ≫ Spec.map (CommRingCat.ofHom ((e).comp c).toRingHom) ≫ toCurve d) :
    p ≫ (V).ι ≫ finiteResolvedSecantOriginalOutput hπ data j hj = q ≫ tan := by
  let f := p ≫ finiteResolvedSecantProjection hπ data j hj
  have hl : f ≫ Spec.map (CommRingCat.ofHom ((e₀).comp a₀).toRingHom) ≫ toCurve d₀ =
      q ≫ Spec.map (CommRingCat.ofHom ((e).comp a).toRingHom) ≫ toCurve d := by
    dsimp only [f]
    rw [Category.assoc, finiteResolvedSecantProjection_left]
    exact ha
  have hr : f ≫ Spec.map (CommRingCat.ofHom ((e₀).comp c₀).toRingHom) ≫ toCurve d₀ =
      q ≫ Spec.map (CommRingCat.ofHom ((e).comp c).toRingHom) ≫ toCurve d := by
    dsimp only [f]
    rw [Category.assoc, finiteResolvedSecantProjection_right]
    exact hc
  let b := q ≫ Spec.map (CommRingCat.ofHom (algebraMap R T))
  let _ : Flat (Spec.map (CommRingCat.ofHom (algebraMap R T))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let _ : Flat b := inferInstanceAs (Flat (q ≫ _))
  have hb : f ≫ Spec.map (CommRingCat.ofHom (algebraMap R Q)) = b := by
    simpa only [Category.assoc, toCurve_structure, specAlgHom_structure] using
      congrArg (· ≫ integralCurveStructure W) hl
  have h := dividedCrossDepthTangentSecant_scheme
    W (π ^ k) d.b3 d.b4 d.b6 s₀ (d₀).b3 (d₀).b4 (d₀).b6 a c a₀ c₀
    d.factor3 d.factor4 d.factor6 (d₀).factor3 (d₀).factor4 (d₀).factor6
    b (IsRegular.of_ne_zero (pow_ne_zero _ hπ)) q f rfl hb
    (by simpa only [toCurve, WeierstrassDilatation.toCurve,
          AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp,
          Spec.map_comp, Category.assoc] using hl.symm)
    (by simpa only [toCurve, WeierstrassDilatation.toCurve,
          AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp,
          Spec.map_comp, Category.assoc] using hr.symm)
  simpa only [f, Category.assoc, finiteResolvedSecantProjection_output] using h.symm

/-- Every actual finite-model tangent lift equals the old secant output on this overlap. -/
theorem finiteResolvedSecant_crossDepthTangentOverlap {X : Scheme.{u}}
    (p : X ⟶ (V).toScheme) (q : X ⟶ Spec (.of T)) [Flat q]
    (ha : p ≫ finiteResolvedSecantDomainMap hπ data j hj ≫ pullback.fst t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      q ≫ Spec.map (CommRingCat.ofHom ((e).comp a).toRingHom) ≫ toCurve d)
    (hc : p ≫ finiteResolvedSecantDomainMap hπ data j hj ≫ pullback.snd t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      q ≫ Spec.map (CommRingCat.ofHom ((e).comp c).toRingHom) ≫ toCurve d)
    (z : X ⟶ (U).toScheme)
    (hz : z ≫ (U).ι ≫ finiteGlobalContraction hπ data j hj = q ≫ tan) :
    p ≫ finiteResolvedSecantAddition hπ data j hj = z := by
  apply (cancel_mono (U).ι).mp
  apply finiteGlobal_smooth_output_hom_ext hπ data j hj
    (p ≫ finiteResolvedSecantOriginalSmooth hπ data j hj)
  · simp only [Category.assoc, finiteResolvedSecantAddition_contraction,
      finiteResolvedSecantOriginalSmooth_inclusion]
  · rw [Category.assoc, hz]
    simpa only [Category.assoc, finiteResolvedSecantOriginalSmooth_inclusion] using
      (finiteResolvedSecant_crossDepthTangentOriginal hπ data j hj d a c p q ha hc).symm

end FLT.Mazur.WeierstrassDividedDepth
