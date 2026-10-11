/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtalePolynomialGeometricOpenPoints
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Polynomial coefficient extension is geometric base change

The geometric polynomial chart used to select separable points is the actual
base change of the original affine chart along the coefficient field map.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.PolynomialCoefficientCartesian
open EtalePolynomialGeometricOpenPoints
variable {k K B : Type} [Field k] [Field K] [Algebra k K] [CommRing B] {n : ℕ}
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Extending polynomial coefficients forms the actual cartesian spectrum square. -/
theorem coefficient_isPullback :
    IsPullback (coefficientMap (k := k) (K := K) (n := n))
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)))
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (Fin n) k)))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  exact (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout k K (MvPolynomial (Fin n) k)
      (MvPolynomial (Fin n) K))).flip

/-- The polynomial-chart construction is base change of its original structural morphism. -/
theorem chart_isPullback (g : MvPolynomial (Fin n) k →+* B) :
    IsPullback (pullback.fst (Spec.map (CommRingCat.ofHom g)) (coefficientMap (K := K)))
      (pullback.snd (Spec.map (CommRingCat.ofHom g)) (coefficientMap (K := K)) ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)))
      (Spec.map (CommRingCat.ofHom (g.comp MvPolynomial.C)))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  have h := (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom g))
    (coefficientMap (K := K))).paste_vert (coefficient_isPullback (k := k) (K := K))
  simpa only [← Spec.map_comp, CommRingCat.ofHom_comp] using h

end FLT.Mazur.PolynomialCoefficientCartesian
