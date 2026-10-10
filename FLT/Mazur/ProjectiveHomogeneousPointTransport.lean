/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveHomogeneousPoint
public import FLT.Mazur.ProjectiveLinearIsomorphism

/-!
# Transport of evaluated projective scheme points

Graded substitutions transport the actual scheme morphisms on homogeneous
charts. For an invertible linear substitution, a standard chart pulls back
to the basic open of the corresponding linear form.
-/

@[expose] public noncomputable section
open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R T S : Type u} [CommRing R] [CommRing T] [CommRing S]
variable {ι κ : Type u}

/-- Evaluation transports through the actual morphism induced by a graded map. -/
lemma homogeneousPoint_gradedMap (g : grading T κ →+*ᵍ grading R ι)
    (hg : HomogeneousIdeal.irrelevant (grading R ι) ≤
      (HomogeneousIdeal.irrelevant (grading T κ)).map g)
    (F : MvPolynomial ι R →+* S) (s : MvPolynomial κ T)
    {m : ℕ} (hm : s ∈ grading T κ m) (hpos : 0 < m)
    (a : Sˣ) (ha : F (g s) = a) :
    homogeneousPoint R ι F (g s) (g.map_mem hm) hpos a ha ≫ Proj.map g hg =
      homogeneousPoint T κ (F.comp g.toRingHom) s hm hpos a ha := by
  rw [homogeneousPoint, Category.assoc, Proj.awayι_comp_map g hg hpos s hm]
  rw [← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
      ((homogeneousEval R ι F (g s) a ha).comp (Away.map g s))) ≫ _ = _
  rw [homogeneousEval_gradedMap R ι g F s a ha hm]
  rfl

/-- The preimage of a standard chart is the basic open of the inverse linear form. -/
lemma linearIso_preimage_chart (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R)) (j : κ) :
    (linearIso e).hom ⁻¹ᵁ chart R κ j =
      Proj.basicOpen (grading R ι) (linearForm (e.symm (Finsupp.single j 1))) := by
  change Proj.basicOpen (grading R ι) (linearGradedMap e.symm.toLinearMap (X j)) = _
  rw [show linearGradedMap e.symm.toLinearMap (X j) =
    linearForm (e.symm (Finsupp.single j 1)) from linearSubstitution_X _ _]

/-- A polynomial evaluation comparison gives equality of actual scheme points. -/
lemma unitChartPoint_linearIso_of_eval (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R))
    (f : R →+* S) (x : ι → S) (y : κ → S)
    (h : (eval₂Hom f x).comp (linearGradedMap e.symm.toLinearMap).toRingHom =
      eval₂Hom f y) (i : ι) (j : κ) (a b : Sˣ) (hi : x i = a) (hj : y j = b) :
    unitChartPoint R ι f x i a hi ≫ (linearIso e).hom =
      unitChartPoint R κ f y j b hj := by
  let g := linearGradedMap e.symm.toLinearMap
  have hb : eval₂Hom f x (g (X j)) = b := by
    have he := DFunLike.congr_fun h (X j)
    exact he.trans ((eval₂_X f y j).trans hj)
  rw [← homogeneousPoint_variable R ι f x i a hi]
  rw [homogeneousPoint_change R ι (eval₂Hom f x) (X i) (g (X j))
    (isHomogeneous_X R i) (g.map_mem (isHomogeneous_X R j))
    (by decide) (by decide) a b (by simpa using hi) hb]
  change homogeneousPoint R ι (eval₂Hom f x) (g (X j)) _ _ b hb ≫
    Proj.map g (linearGradedMap_irrelevant e.symm) = _
  rw [homogeneousPoint_gradedMap g (linearGradedMap_irrelevant e.symm)
    (eval₂Hom f x) (X j) (isHomogeneous_X R j) (by decide) b hb]
  simp only [g, h]
  exact homogeneousPoint_variable R κ f y j b hj

end FLT.Mazur.ProjectiveSpace
