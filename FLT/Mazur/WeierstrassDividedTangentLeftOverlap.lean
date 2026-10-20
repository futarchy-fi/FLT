/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentSchemeAction
public import FLT.Mazur.WeierstrassDividedTangentOverlapProjections
public import FLT.Mazur.WeierstrassDividedGlobalFiniteSmoothActionUnique

/-!
# Agreement of the actual resolved additions on the left-input overlap

Compare the original actions using the two retained inputs. The new output
is originally smooth, so unchanged-smooth-output uniqueness identifies the
resolved lifts, without asserting injectivity of the entire contraction.
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
local notation "v" => integralSmoothStructure W
local notation "V" => finiteResolvedTangentOutputOpen hπ data j hj

variable {X : Scheme.{u}} (p : X ⟶ (finiteResolvedTangentOutputOpen hπ data j hj).toScheme)
  (q : X ⟶ pullback (integralSmoothStructure W)
    ((finiteGlobalStructure hπ data j hj).smoothLocus.ι ≫ finiteGlobalStructure hπ data j hj))
  (hpq : p ≫ finiteResolvedTangentDomainMap hπ data j hj =
    q ≫ finiteResolvedLeftInput hπ data j hj)

include hpq in
/-- The two actual original actions agree on every refinement of the left-input overlap. -/
theorem finiteResolvedTangent_leftOriginalAction :
    p ≫ (V).ι ≫ finiteResolvedTangentOriginalOutput hπ data j hj =
      (q ≫ finiteGlobalSmoothAction hπ data j hj) ≫ (U).ι ≫
        finiteGlobalContraction hπ data j hj := by
  let f := p ≫ finiteResolvedTangentProjection hπ data j hj
  have hl : f ≫ Spec.map (CommRingCat.ofHom
      ((IsScalarTower.toAlgHom R P T).comp a).toRingHom) ≫ toCurve d =
        (q ≫ pullback.fst v t) ≫ (integralSmoothOpen W).ι := by
    dsimp only [f]
    rw [Category.assoc, finiteResolvedTangentProjection_left,
      ← Category.assoc p (finiteResolvedTangentDomainMap hπ data j hj), hpq,
      Category.assoc, finiteResolvedLeftInput_fst_assoc,
      finiteOriginalToResolved_inclusion_assoc, finiteGlobalSmoothEmbedding_contraction]
    simp only [Category.assoc]
  have hr : f ≫ Spec.map (CommRingCat.ofHom
      ((IsScalarTower.toAlgHom R P T).comp c).toRingHom) ≫ toCurve d =
        q ≫ pullback.snd v t ≫ (U).ι ≫ finiteGlobalContraction hπ data j hj := by
    dsimp only [f]
    rw [Category.assoc, finiteResolvedTangentProjection_right,
      ← Category.assoc p (finiteResolvedTangentDomainMap hπ data j hj), hpq,
      Category.assoc, finiteResolvedLeftInput_snd_assoc]
  have hb : (q ≫ pullback.fst v t) ≫ v =
      (f ≫ Spec.map (CommRingCat.ofHom
        ((IsScalarTower.toAlgHom R P T).comp c).toRingHom) ≫ toCurve d) ≫
          integralCurveStructure W := by
    rw [hr]
    simpa only [Category.assoc, finiteGlobalStructure] using
      congrArg (q ≫ ·) (pullback.condition (f := v) (g := t))
  have h := dividedTangent_schemeAction W s (d).b3 (d).b4 (d).b6 a c
    (d).factor3 (d).factor4 (d).factor6 f (q ≫ pullback.fst v t) hl hb
  dsimp only [WeierstrassDividedDepth.toCurve] at hr
  simp only [hr] at h
  rw [finiteGlobalSmoothAction, ← finiteGlobalSmoothPointAction_comp,
    finiteGlobalSmoothPointAction_contraction]
  simpa only [f, Category.assoc, finiteResolvedTangentProjection_output] using h

include hpq in
/-- The new and old resolved lifts coincide on the actual left-original-smooth overlap. -/
theorem finiteResolvedTangent_leftOverlap :
    p ≫ finiteResolvedTangentAddition hπ data j hj =
      q ≫ finiteGlobalSmoothAction hπ data j hj := by
  apply (cancel_mono (U).ι).mp
  apply finiteGlobal_smooth_output_hom_ext hπ data j hj
    (p ≫ finiteResolvedTangentOriginalSmooth hπ data j hj)
  · simp only [Category.assoc, finiteResolvedTangentAddition_contraction,
      finiteResolvedTangentOriginalSmooth_inclusion]
  · simp only [Category.assoc, finiteResolvedTangentOriginalSmooth_inclusion]
    exact (finiteResolvedTangent_leftOriginalAction hπ data j hj p q hpq).symm

end FLT.Mazur.WeierstrassDividedDepth
