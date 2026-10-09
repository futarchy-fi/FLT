/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartTupleTransitionTests
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Comparing two intrinsic parameters on affine tests

An affine test lying in both basis loci factors through the actual transition
domain. Its two intrinsic classifying morphisms are related by that transition.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Type u) (d : ℕ)
variable (w v : Fin d → MvPolynomial I R)
variable (S : Type u) [CommRing S] [Algebra R S] (J : Ideal (MvPolynomial I S))
variable [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]
variable [Module.Flat S (MvPolynomial I S ⧸ J)]
variable (T : Type u) [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- Two affine tests of the same family give the actual change-of-tuple parameter. -/
theorem intrinsicChartMorphism_affineTupleComparison
    (f : Spec (.of T) ⟶ polynomialBasisScheme R I d w S J)
    (g : Spec (.of T) ⟶ polynomialBasisScheme R I d v S J)
    (hf : f ≫ Scheme.Opens.ι (X := Spec (.of S)) (polynomialBasisOpen R I d w S J) =
      Spec.map (CommRingCat.ofHom (algebraMap S T)))
    (hg : g ≫ Scheme.Opens.ι (X := Spec (.of S)) (polynomialBasisOpen R I d v S J) =
      Spec.map (CommRingCat.ofHom (algebraMap S T))) :
    ∃ k : Spec (.of T) ⟶ (chartTupleTransitionOpen R I d w v).toScheme,
      k ≫ (chartTupleTransitionOpen R I d w v).ι =
        f ≫ intrinsicChartMorphism R I d w S J ∧
      k ≫ chartTupleTransition R I d w v = g ≫ intrinsicChartMorphism R I d v S J := by
  have hw := (polynomialBasisScheme_affineFactorization_iff R I d w S J T).mp
    ⟨f, hf, fun a ha ↦ (cancel_mono (Scheme.Opens.ι (X := Spec (.of S))
      (polynomialBasisOpen R I d w S J))).mp
      (ha.trans hf.symm)⟩
  have hv := (polynomialBasisScheme_affineFactorization_iff R I d v S J T).mp
    ⟨g, hg, fun a ha ↦ (cancel_mono (Scheme.Opens.ι (X := Spec (.of S))
      (polynomialBasisOpen R I d v S J))).mp
      (ha.trans hg.symm)⟩
  let a := idealClassifyingMap R I d w T ⟨_, hw⟩
  let b := idealClassifyingMap R I d v T ⟨_, hv⟩
  have ha : pointIdeal R I d w a = J.map (MvPolynomial.map (algebraMap S T)) :=
    congrArg Subtype.val (idealOfPoint_idealClassifyingMap R I d w T ⟨_, hw⟩)
  have hb : pointIdeal R I d v b = J.map (MvPolynomial.map (algebraMap S T)) :=
    congrArg Subtype.val (idealOfPoint_idealClassifyingMap R I d v T ⟨_, hv⟩)
  have hv' : ∃ q : Module.Basis (Fin d) T (MvPolynomial I T ⧸ pointIdeal R I d w a),
      ∀ i, polynomialBasisTuple R I d v T (pointIdeal R I d w a) i = q i := by
    rw [ha]
    exact hv
  obtain ⟨k, hk, _⟩ := (chartTupleTransition_factorization_iff R I d w v a).mpr hv'
  refine ⟨k, hk.trans (intrinsicChartMorphism_affineTest R I d w S J T hw f hf).symm, ?_⟩
  exact (chartTupleTransition_affineTest_eq R I d w v a k hk b (hb.trans ha.symm)).trans
    (intrinsicChartMorphism_affineTest R I d v S J T hv g hg).symm

omit [Algebra S T] [Algebra R T] [IsScalarTower R S T] in
/-- The affine comparison needs only equality of the maps to the original base. -/
theorem intrinsicChartMorphism_affineTupleComparison_over
    (f : Spec (.of T) ⟶ polynomialBasisScheme R I d w S J)
    (g : Spec (.of T) ⟶ polynomialBasisScheme R I d v S J)
    (h : f ≫ Scheme.Opens.ι (X := Spec (.of S)) (polynomialBasisOpen R I d w S J) =
      g ≫ Scheme.Opens.ι (X := Spec (.of S)) (polynomialBasisOpen R I d v S J)) :
    ∃ k : Spec (.of T) ⟶ (chartTupleTransitionOpen R I d w v).toScheme,
      k ≫ (chartTupleTransitionOpen R I d w v).ι =
        f ≫ intrinsicChartMorphism R I d w S J ∧
      k ≫ chartTupleTransition R I d w v = g ≫ intrinsicChartMorphism R I d v S J := by
  let a := (Spec.preimage (f ≫ Scheme.Opens.ι (X := Spec (.of S))
    (polynomialBasisOpen R I d w S J))).hom
  let _ : Algebra S T := a.toAlgebra
  let _ : Algebra R T := (a.comp (algebraMap R S)).toAlgebra
  let _ : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hf : f ≫ Scheme.Opens.ι (X := Spec (.of S)) (polynomialBasisOpen R I d w S J) =
      Spec.map (CommRingCat.ofHom (algebraMap S T)) := (Spec.map_preimage _).symm
  exact intrinsicChartMorphism_affineTupleComparison R I d w v S J T f g hf
    (h.symm.trans hf)

end FLT.Mazur.HilbertChart
