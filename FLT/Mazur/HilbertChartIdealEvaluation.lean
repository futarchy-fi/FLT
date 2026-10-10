/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartTupleTransition
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Preserving chart ideals under ambient affine tests

A test of the ambient polynomial space specifies both a coefficient parameter
and values of the polynomial variables. Over a chart transition, evaluating
the two universal ideals gives the same full ideal in the test ring.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

/-- A polynomial homomorphism factors through coefficient extension and variable evaluation. -/
theorem polynomialHom_factor {A B I : Type*} [CommRing A] [CommRing B]
    (f : MvPolynomial I A →+* B) :
    f = (MvPolynomial.eval₂Hom (RingHom.id B) (fun i ↦ f (MvPolynomial.X i))).comp
      (MvPolynomial.map (f.comp MvPolynomial.C)) := by
  ext a <;> simp

variable (R : Type u) [CommRing R] (I : Type u) (d : ℕ)
variable (w v : Fin d → MvPolynomial I R)

/-- Cache the coefficient ring for ambient ideal inference. -/
local instance evaluationCoefficientsRing : CommRing (Coefficients R I d) := inferInstance
/-- Cache the source chart ring for ambient ideal inference. -/
local instance evaluationSourceRing : CommRing (ChartRing R I d w) := inferInstance
/-- Cache the target chart ring for ambient ideal inference. -/
local instance evaluationTargetRing : CommRing (ChartRing R I d v) := inferInstance

/-- Ambient affine tests of a transition preserve the entire universal ideal. -/
theorem chartIdentityIdeal_transition_evaluation {S : Type u} [CommRing S]
    (F : MvPolynomial I (ChartRing R I d w) →+* S)
    (G : MvPolynomial I (ChartRing R I d v) →+* S)
    (g : Spec (.of S) ⟶ (chartTupleTransitionOpen R I d w v).toScheme)
    (hF : g ≫ (chartTupleTransitionOpen R I d w v).ι =
      Spec.map (CommRingCat.ofHom (F.comp MvPolynomial.C)))
    (hG : g ≫ chartTupleTransition R I d w v =
      Spec.map (CommRingCat.ofHom (G.comp MvPolynomial.C)))
    (hX : ∀ i, F (MvPolynomial.X i) = G (MvPolynomial.X i)) :
    (chartIdentityIdeal R I d w).map F = (chartIdentityIdeal R I d v).map G := by
  let a₀ := F.comp MvPolynomial.C
  let _ : Algebra R S := (a₀.comp (algebraMap R (ChartRing R I d w))).toAlgebra
  let a : ChartRing R I d w →ₐ[R] S := ⟨a₀, fun _ ↦ rfl⟩
  obtain ⟨b, hb, hi⟩ := chartTupleTransition_affineTest R I d w v a g hF
  have hcoeff : G.comp MvPolynomial.C = b.toRingHom := by
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective (hG.symm.trans hb))
  have hi' : (chartIdentityIdeal R I d w).map (MvPolynomial.map a₀) =
      (chartIdentityIdeal R I d v).map (MvPolynomial.map (G.comp MvPolynomial.C)) := by
    rw [hcoeff, chartIdentityIdeal_map R I d v b]
    exact (chartIdentityIdeal_map R I d w a).trans hi.symm
  have he := congrArg (Ideal.map
    (MvPolynomial.eval₂Hom (RingHom.id S) (fun i ↦ F (MvPolynomial.X i)))) hi'
  rw [Ideal.map_map, Ideal.map_map] at he
  have hvar : (fun i ↦ F (MvPolynomial.X i)) = fun i ↦ G (MvPolynomial.X i) := funext hX
  rw [← polynomialHom_factor F, hvar, ← polynomialHom_factor G] at he
  exact he

end FLT.Mazur.HilbertChart
