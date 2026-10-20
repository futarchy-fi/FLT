/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentSchemeAction
public import FLT.Mazur.WeierstrassDividedResolvedProductOverlap
public import FLT.Mazur.WeierstrassDividedTangentFlatSourceExt
public import FLT.Mazur.WeierstrassDividedGlobalFiniteSmoothActionUnique

/-!
# Independent-depth tangent lifts on the originally smooth left-input domain

The actual left action has the supplied tangent contraction. Flat-source
uniqueness identifies every constructed finite-model lift of that formula.
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
local notation "T" => DividedTangentRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "e" => IsScalarTower.toAlgHom R S T
local notation "U" => (finiteGlobalStructure hπ data j hj).smoothLocus
local notation "t" => (U).ι ≫ finiteGlobalStructure hπ data j hj
local notation "v" => integralSmoothStructure W
local notation "tan" => dividedTangentToCurve W (π ^ k) d.b3 d.b4 d.b6 a c
  d.factor3 d.factor4 d.factor6

omit [Module.Flat R S] in
/-- The left action contracts to the independent-depth tangent with the same original inputs. -/
theorem finiteResolvedLeft_crossDepthTangentOriginal {X : Scheme.{u}}
    (p : X ⟶ pullback v t) (q : X ⟶ Spec (.of T))
    (ha : p ≫ finiteResolvedLeftInput hπ data j hj ≫ pullback.fst t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      q ≫ Spec.map (CommRingCat.ofHom ((e).comp a).toRingHom) ≫ toCurve d)
    (hc : p ≫ finiteResolvedLeftInput hπ data j hj ≫ pullback.snd t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      q ≫ Spec.map (CommRingCat.ofHom ((e).comp c).toRingHom) ≫ toCurve d) :
    (p ≫ finiteGlobalSmoothAction hπ data j hj) ≫ (U).ι ≫
        finiteGlobalContraction hπ data j hj = q ≫ tan := by
  have hl : q ≫ Spec.map (CommRingCat.ofHom ((e).comp a).toRingHom) ≫ toCurve d =
      (p ≫ pullback.fst v t) ≫ (integralSmoothOpen W).ι := by
    simpa only [Category.assoc, finiteResolvedLeftInput_fst_assoc,
      finiteOriginalToResolved_inclusion_assoc, finiteGlobalSmoothEmbedding_contraction]
      using ha.symm
  have hr : q ≫ Spec.map (CommRingCat.ofHom ((e).comp c).toRingHom) ≫ toCurve d =
      p ≫ pullback.snd v t ≫ (U).ι ≫ finiteGlobalContraction hπ data j hj := by
    simpa only [Category.assoc, finiteResolvedLeftInput_snd_assoc] using hc.symm
  have hb : (p ≫ pullback.fst v t) ≫ v =
      (q ≫ Spec.map (CommRingCat.ofHom ((e).comp c).toRingHom) ≫ toCurve d) ≫
        integralCurveStructure W := by
    rw [hr]
    simpa only [Category.assoc, finiteGlobalStructure] using
      congrArg (p ≫ ·) (pullback.condition (f := v) (g := t))
  have h := dividedTangent_schemeAction W (π ^ k) d.b3 d.b4 d.b6 a c
    d.factor3 d.factor4 d.factor6 q (p ≫ pullback.fst v t) hl hb
  dsimp only [WeierstrassDividedDepth.toCurve] at hr
  simp only [hr] at h
  rw [finiteGlobalSmoothAction, ← finiteGlobalSmoothPointAction_comp,
    finiteGlobalSmoothPointAction_contraction]
  exact h.symm

/-- A flat tangent refinement determines the actual left-action lift without output smoothness. -/
theorem finiteResolvedLeft_crossDepthTangentOverlap {X : Scheme.{u}}
    (p : X ⟶ pullback v t) (q : X ⟶ Spec (.of T)) [Flat q]
    (ha : p ≫ finiteResolvedLeftInput hπ data j hj ≫ pullback.fst t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      q ≫ Spec.map (CommRingCat.ofHom ((e).comp a).toRingHom) ≫ toCurve d)
    (hc : p ≫ finiteResolvedLeftInput hπ data j hj ≫ pullback.snd t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      q ≫ Spec.map (CommRingCat.ofHom ((e).comp c).toRingHom) ≫ toCurve d)
    (z : X ⟶ (U).toScheme)
    (hz : z ≫ (U).ι ≫ finiteGlobalContraction hπ data j hj = q ≫ tan) :
    p ≫ finiteGlobalSmoothAction hπ data j hj = z := by
  apply (cancel_mono (U).ι).mp
  apply finiteTangentOutput_ext hπ data hj d a c q
  · simpa only [Category.assoc] using
      finiteResolvedLeft_crossDepthTangentOriginal hπ data j hj d a c p q ha hc
  · simpa only [Category.assoc] using hz

end FLT.Mazur.WeierstrassDividedDepth
