/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineMorphismAlgebraMap
public import FLT.Mazur.HilbertPolynomialFamilyAffineTest
public import FLT.Mazur.HilbertPolynomialParameterChart
public import FLT.Mazur.HilbertPolynomialParameterDegree

/-!
# Recovering arbitrary Hilbert parameters on chart tests

Classifying the actual pulled-back quotient recovers the original parameter
on every affine chart test. Affine covers extend this to all scheme tests
factoring through a Hilbert chart.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (S : Type u) [CommRing S] [Algebra R S]
variable (f : Spec (.of S) ⟶ polynomialHilbertScheme R I d)
variable (hf : f ≫ polynomialHilbertStructure R I d =
  Spec.map (CommRingCat.ofHom (algebraMap R S)))

/-- Reclassify the actual finite flat quotient pulled back from the parameter. -/
def polynomialParameterClassifyingMorphism : Spec (.of S) ⟶ polynomialHilbertScheme R I d :=
  polynomialFamilyMorphism R I d S (polynomialParameterIdeal R I d S f hf)
    (polynomialParameterIdeal_residueRank R I d S f hf)

/-- Every affine chart test recovers the original parameter after quotient classification. -/
theorem polynomialParameterClassifyingMorphism_affineTest
    (T : Type u) [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (w : Fin d → MvPolynomial I R) (a : ChartRing R I d w →ₐ[R] T)
    (ha : Spec.map (CommRingCat.ofHom (algebraMap S T)) ≫ f =
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ polynomialHilbertChartι R I d w) :
    Spec.map (CommRingCat.ofHom (algebraMap S T)) ≫
        polynomialParameterClassifyingMorphism R I d S f hf =
      Spec.map (CommRingCat.ofHom (algebraMap S T)) ≫ f := by
  rw [ha]
  exact polynomialFamilyMorphism_affineTest R I d S (polynomialParameterIdeal R I d S f hf)
    (polynomialParameterIdeal_residueRank R I d S f hf) T w a
      (polynomialParameterIdeal_affineChart R I d S f hf T w a ha).symm

/-- A scheme test in a Hilbert chart recovers the parameter without an affine-source assumption. -/
theorem polynomialParameterClassifyingMorphism_schemeTest
    (w : Fin d → MvPolynomial I R) {X : Scheme.{u}}
    (g : X ⟶ Spec (.of S)) (k : X ⟶ Spec (.of (ChartRing R I d w)))
    (h : g ≫ f = k ≫ polynomialHilbertChartι R I d w) :
    g ≫ polynomialParameterClassifyingMorphism R I d S f hf = g ≫ f := by
  apply X.affineOpenCover.openCover.hom_ext
  intro i
  let T := X.affineOpenCover.X i
  let a := (Spec.preimage (X.affineOpenCover.f i ≫ g)).hom
  let _ : Algebra S T := a.toAlgebra
  let _ : Algebra R T := (a.comp (algebraMap R S)).toAlgebra
  let _ : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have ha : Spec.map (CommRingCat.ofHom (algebraMap S T)) =
      X.affineOpenCover.f i ≫ g := Spec.map_preimage _
  have hk : (X.affineOpenCover.f i ≫ k) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing R I d w))) =
      Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
    rw [← polynomialHilbertChartι_over R I d w, Category.assoc, ← Category.assoc k,
      ← h, ← Category.assoc, ← Category.assoc, ← ha, Category.assoc, hf, ← Spec.map_comp]
    rfl
  let b := affineOverAlgHom R (ChartRing R I d w) T (X.affineOpenCover.f i ≫ k) hk
  have hb : Spec.map (CommRingCat.ofHom b.toRingHom) = X.affineOpenCover.f i ≫ k :=
    affineOverAlgHom_spec R (ChartRing R I d w) T _ hk
  have he : Spec.map (CommRingCat.ofHom (algebraMap S T)) ≫ f =
      Spec.map (CommRingCat.ofHom b.toRingHom) ≫ polynomialHilbertChartι R I d w := by
    rw [ha, hb, Category.assoc, Category.assoc, h]
  have hr := polynomialParameterClassifyingMorphism_affineTest R I d S f hf T w b he
  rw [ha, Category.assoc, Category.assoc] at hr
  exact hr

end FLT.Mazur.HilbertChart
