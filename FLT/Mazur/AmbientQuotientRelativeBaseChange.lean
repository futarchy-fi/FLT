/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientQuotientRelativeSpace

/-!
# Base change maps of actual affine quotient ambient spaces

Actual quotient ambient spaces form cartesian squares over arbitrary maps of
scheme bases. The constructed maps preserve the original quotient coordinates
and their closed immersions in relative quotient space.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (K : Ideal (MvPolynomial I R))
variable {X Y Z : Scheme.{u}}
variable (s : X ⟶ Spec (.of R)) (t : Y ⟶ Spec (.of R))

/-- A morphism over the coefficient ring induces a map of relative quotient ambient spaces. -/
def quotientRelativeAmbientMap (g : Y ⟶ X) (hg : g ≫ s = t) :
    quotientRelativeAmbient R I K t ⟶ quotientRelativeAmbient R I K s :=
  pullback.lift (pullback.fst _ _ ≫ g) (pullback.snd _ _) (by
    rw [Category.assoc, hg]
    exact pullback.condition)

/-- The ambient morphism lies over the given morphism of bases. -/
@[reassoc]
theorem quotientRelativeAmbientMap_fst (g : Y ⟶ X) (hg : g ≫ s = t) :
    quotientRelativeAmbientMap R I K s t g hg ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ g := pullback.lift_fst _ _ _

/-- The ambient morphism preserves the original quotient-space projection. -/
@[reassoc]
theorem quotientRelativeAmbientMap_snd (g : Y ⟶ X) (hg : g ≫ s = t) :
    quotientRelativeAmbientMap R I K s t g hg ≫ pullback.snd _ _ =
      pullback.snd _ _ := pullback.lift_snd _ _ _

/-- Relative quotient ambient maps form actual cartesian squares over their base maps. -/
theorem quotientRelativeAmbientMap_isPullback (g : Y ⟶ X) (hg : g ≫ s = t) :
    IsPullback (quotientRelativeAmbientMap R I K s t g hg) (pullback.fst _ _)
      (pullback.fst _ _) g := by
  have h : IsPullback (pullback.fst t
      (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial I R ⧸ K)))))
      (quotientRelativeAmbientMap R I K s t g hg ≫ pullback.snd _ _) (g ≫ s)
      (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial I R ⧸ K)))) := by
    rw [quotientRelativeAmbientMap_snd, hg]
    exact IsPullback.of_hasPullback _ _
  exact (h.of_bot (quotientRelativeAmbientMap_fst R I K s t g hg).symm
    (IsPullback.of_hasPullback _ _)).flip

/-- Relative quotient ambient maps preserve identity morphisms. -/
theorem quotientRelativeAmbientMap_id :
    quotientRelativeAmbientMap R I K s s (𝟙 X) (Category.id_comp s) = 𝟙 _ := by
  apply pullback.hom_ext <;>
    simp only [quotientRelativeAmbientMap_fst, quotientRelativeAmbientMap_snd,
      Category.id_comp, Category.comp_id]

/-- Relative quotient ambient maps preserve composition of base morphisms. -/
theorem quotientRelativeAmbientMap_comp (r : Z ⟶ Spec (.of R))
    (g : Y ⟶ X) (hg : g ≫ s = t) (h : Z ⟶ Y) (hh : h ≫ t = r) :
    quotientRelativeAmbientMap R I K t r h hh ≫ quotientRelativeAmbientMap R I K s t g hg =
      quotientRelativeAmbientMap R I K s r (h ≫ g) (by rw [Category.assoc, hg, hh]) := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, quotientRelativeAmbientMap_fst,
      quotientRelativeAmbientMap_snd, quotientRelativeAmbientMap_fst_assoc]

/-- Base change preserves the actual closed immersion in relative polynomial space. -/
theorem quotientRelativeAmbientMap_immersion (g : Y ⟶ X) (hg : g ≫ s = t) :
    quotientRelativeAmbientMap R I K s t g hg ≫ quotientRelativeImmersion R I K s =
      quotientRelativeImmersion R I K t ≫ polynomialRelativeAmbientMap R I s t g hg := by
  apply pullback.hom_ext
  · simp only [Category.assoc, quotientRelativeImmersion_fst,
      quotientRelativeAmbientMap_fst, polynomialRelativeAmbientMap_fst,
      quotientRelativeImmersion_fst_assoc]
  · simp only [Category.assoc, quotientRelativeImmersion_snd,
      quotientRelativeAmbientMap_snd_assoc, polynomialRelativeAmbientMap_snd]

end FLT.Mazur.HilbertChart
