/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolynomialSpectrumBaseChangeCover

/-!
# Polynomial ambient spaces over arbitrary schemes

Polynomial space over a scheme is the actual fiber product with polynomial
space over its coefficient ring. Maps over that ring induce cartesian maps
of ambient spaces and satisfy identity and composition laws.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R]
variable {X Y Z : Scheme.{u}}
variable (s : X ⟶ Spec (.of R)) (t : Y ⟶ Spec (.of R))

/-- Actual relative polynomial space over a scheme with a coefficient-ring structure map. -/
def polynomialRelativeAmbient : Scheme.{u} :=
  pullback s (Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := R) (σ := I))))

/-- A morphism over the coefficient ring induces a map of relative polynomial spaces. -/
def polynomialRelativeAmbientMap (g : Y ⟶ X) (hg : g ≫ s = t) :
    polynomialRelativeAmbient R I t ⟶ polynomialRelativeAmbient R I s :=
  pullback.lift (pullback.fst _ _ ≫ g) (pullback.snd _ _) (by
    rw [Category.assoc, hg]
    exact pullback.condition)

/-- The ambient morphism lies over the given morphism of bases. -/
@[reassoc]
theorem polynomialRelativeAmbientMap_fst (g : Y ⟶ X) (hg : g ≫ s = t) :
    polynomialRelativeAmbientMap R I s t g hg ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ g := pullback.lift_fst _ _ _

/-- The ambient morphism preserves the original polynomial-space projection. -/
@[reassoc]
theorem polynomialRelativeAmbientMap_snd (g : Y ⟶ X) (hg : g ≫ s = t) :
    polynomialRelativeAmbientMap R I s t g hg ≫ pullback.snd _ _ =
      pullback.snd _ _ := pullback.lift_snd _ _ _

/-- Relative polynomial ambient maps form actual cartesian squares over their base maps. -/
theorem polynomialRelativeAmbientMap_isPullback (g : Y ⟶ X) (hg : g ≫ s = t) :
    IsPullback (polynomialRelativeAmbientMap R I s t g hg) (pullback.fst _ _)
      (pullback.fst _ _) g := by
  have h : IsPullback (pullback.fst t
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := R) (σ := I)))))
      (polynomialRelativeAmbientMap R I s t g hg ≫ pullback.snd _ _) (g ≫ s)
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := R) (σ := I)))) := by
    rw [polynomialRelativeAmbientMap_snd, hg]
    exact IsPullback.of_hasPullback _ _
  exact (h.of_bot (polynomialRelativeAmbientMap_fst R I s t g hg).symm
    (IsPullback.of_hasPullback _ _)).flip

/-- Relative polynomial ambient maps preserve identity morphisms. -/
theorem polynomialRelativeAmbientMap_id :
    polynomialRelativeAmbientMap R I s s (𝟙 X) (Category.id_comp s) = 𝟙 _ := by
  apply pullback.hom_ext <;>
    simp only [polynomialRelativeAmbientMap_fst, polynomialRelativeAmbientMap_snd,
      Category.id_comp, Category.comp_id]

/-- Relative polynomial ambient maps preserve composition of base morphisms. -/
theorem polynomialRelativeAmbientMap_comp (r : Z ⟶ Spec (.of R))
    (g : Y ⟶ X) (hg : g ≫ s = t) (h : Z ⟶ Y) (hh : h ≫ t = r) :
    polynomialRelativeAmbientMap R I t r h hh ≫ polynomialRelativeAmbientMap R I s t g hg =
      polynomialRelativeAmbientMap R I s r (h ≫ g) (by rw [Category.assoc, hg, hh]) := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, polynomialRelativeAmbientMap_fst,
      polynomialRelativeAmbientMap_snd, polynomialRelativeAmbientMap_fst_assoc]

end FLT.Mazur.HilbertChart
