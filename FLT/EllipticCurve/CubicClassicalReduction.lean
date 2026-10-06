/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicValuativeSpecialization

/-! # Good-model reduction as a homomorphism of classical elliptic-curve point groups -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonObj
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem infinity_preimage_affineChart :
    infinity W ⁻¹ᵁ (affineChart W).opensRange = ⊥ := by
  rw [infinity, Scheme.Hom.comp_preimage]
  have hi : infinityChart W ⁻¹ᵁ (affineChart W).opensRange =
      PrimeSpectrum.basicOpen (coord W true 1) :=
    sourceChart_preimage_opposite W true
  rw [hi]
  change Spec.map (CommRingCat.ofHom (InfinityChart.origin W).toRingHom) ⁻¹ᵁ
    PrimeSpectrum.basicOpen (coord W true 1) = ⊥
  rw [SpecMap_preimage_basicOpen]
  simp [infinity_origin_coord]

theorem affineFieldPoint_ne_infinity {K : Type u} [Field K] [Algebra R K]
    (f : Ring W false →ₐ[R] K) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ affineChart W ≠
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ infinity W := by
  intro h
  have hh := congrArg (fun k ↦ k ⁻¹ᵁ (affineChart W).opensRange) h
  have he : (⊤ : (Spec (.of K)).Opens) = ⊥ := by
    simpa only [Scheme.Hom.comp_preimage, Scheme.Hom.preimage_opensRange,
      infinity_preimage_affineChart, Scheme.Hom.preimage_top, Scheme.Hom.preimage_bot] using hh
  exact top_ne_bot he

/-- Distinct classical points give distinct morphisms into the glued cubic. -/
theorem fieldPointMorphism_injective {K : Type u} [Field K] [Algebra R K] :
    Function.Injective (fieldPointMorphism W (K := K)) := by
  intro P Q h
  cases P with
  | zero =>
    cases Q with
    | zero => rfl
    | some x y hQ =>
      exact (affineFieldPoint_ne_infinity W (affineEvaluation W x y hQ.1) h.symm).elim
  | some x y hP =>
    cases Q with
    | zero =>
      exact (affineFieldPoint_ne_infinity W (affineEvaluation W x y hP.1) h).elim
    | some z t hQ =>
      have he : Spec.map (CommRingCat.ofHom (affineEvaluation W x y hP.1).toRingHom) =
          Spec.map (CommRingCat.ofHom (affineEvaluation W z t hQ.1).toRingHom) :=
        (cancel_mono (affineChart W)).mp h
      have hr := Spec.map_injective he
      have hx := congrArg
        (fun (f : CommRingCat.of (Ring W false) ⟶ CommRingCat.of K) ↦ f (coord W false 0)) hr
      have hy := congrArg
        (fun (f : CommRingCat.of (Ring W false) ⟶ CommRingCat.of K) ↦ f (coord W false 1)) hr
      change affineEvaluation W x y hP.1 (coord W false 0) =
        affineEvaluation W z t hQ.1 (coord W false 0) at hx
      change affineEvaluation W x y hP.1 (coord W false 1) =
        affineEvaluation W z t hQ.1 (coord W false 1) at hy
      simp only [affineEvaluation_coord, Matrix.cons_val_zero] at hx
      simp only [affineEvaluation_coord, Matrix.cons_val_one, Matrix.cons_val_zero] at hy
      subst z
      subst t
      rfl

/-- The actual group of field-valued scheme points is the classical elliptic-curve point group. -/
def classicalPointEquiv [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic]
    (K : Type u) [Field K] [Algebra R K] [DecidableEq K] :
    Multiplicative ((W.map (algebraMap R K)).toAffine.Point) ≃*
      (pointSource (R := R) K ⟶ groupModel W) :=
  MulEquiv.ofBijective (classicalPointHom W K) ⟨by
    intro P Q h
    change P.toAdd = Q.toAdd
    apply fieldPointMorphism_injective W
    exact congrArg Over.Hom.left h, by
    intro f
    obtain ⟨P, hP⟩ := fieldPointMorphism_surjective W f.left f.w
    refine ⟨Multiplicative.ofAdd P, ?_⟩
    apply Over.OverMorphism.ext
    exact hP⟩

/-- Reduce every classical generic-fiber point of a good integral Weierstrass model.
The morphism includes points whose ordinary affine coordinates are not integral. -/
def classicalReductionHom [IsDomain R] [ValuationRing R]
    [IsNoetherianRing R] [W.IsElliptic]
    (K k : Type u) [Field K] [Algebra R K] [IsFractionRing R K] [DecidableEq K]
    [Field k] [Algebra R k] [DecidableEq k] :
    (W.map (algebraMap R K)).toAffine.Point →+
      (W.map (algebraMap R k)).toAffine.Point :=
  MonoidHom.toAdditive
    (((classicalPointEquiv W k).symm.toMonoidHom).comp (classicalSpecializationHom W K k))

@[simp] theorem classicalReductionHom_torsion [IsDomain R] [ValuationRing R]
    [IsNoetherianRing R] [W.IsElliptic]
    (K k : Type u) [Field K] [Algebra R K] [IsFractionRing R K] [DecidableEq K]
    [Field k] [Algebra R k] [DecidableEq k]
    (P : (W.map (algebraMap R K)).toAffine.Point) (n : ℕ) (h : n • P = 0) :
    n • classicalReductionHom W K k P = 0 := by
  rw [← map_nsmul, h, map_zero]

end WeierstrassCurve.CubicCharts
