/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveChartPolynomialEquiv

/-!
# The affine chart immersion into projective space

The polynomial chart equivalence gives an open immersion of affine `n`-space
into the existing polynomial Proj model. Its projection to the base is the
usual polynomial projection, via the degree-zero part of the grading.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

universe u v

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.ProjectiveSpace

variable (R : Type u) [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Projective space projects to the coefficient spectrum through degree zero. -/
def baseProjection (R : Type (max u v)) [CommRing R] (ι : Type v) :
    space R ι ⟶ Spec (.of R) :=
  Proj.toSpecZero (grading R ι) ≫ Spec.map (CommRingCat.ofHom (constantsToZero R ι))

variable (n : ℕ)

/-- The spectrum isomorphism induced by the constructed polynomial equivalence. -/
def polynomialChartSpecIso :
    Spec (.of (MvPolynomial (Fin n) R)) ≅
      Spec (.of (chartRing R (Fin (n + 1)) 0)) :=
  Scheme.Spec.mapIso (chartPolynomialEquiv R n).toRingEquiv.toCommRingCatIso.symm.op

/-- Affine space identifies with the zeroth standard projective open. -/
def affineChartIso :
    Spec (.of (MvPolynomial (Fin n) R)) ≅ (chart R (Fin (n + 1)) 0).toScheme :=
  polynomialChartSpecIso R n ≪≫ (chartIso R (Fin (n + 1)) 0).symm

/-- The standard affine-to-projective embedding. -/
def affineChartEmbedding :
    Spec (.of (MvPolynomial (Fin n) R)) ⟶ space R (Fin (n + 1)) :=
  (affineChartIso R n).hom ≫ (chart R (Fin (n + 1)) 0).ι

instance affineChartEmbedding_isOpenImmersion : IsOpenImmersion (affineChartEmbedding R n) := by
  dsimp only [affineChartEmbedding]
  infer_instance

/-- The affine embedding has exactly the zeroth standard chart as its image. -/
lemma affineChartEmbedding_opensRange :
    (affineChartEmbedding R n).opensRange = chart R (Fin (n + 1)) 0 := by
  exact (Scheme.Hom.opensRange_comp_of_isIso _ _).trans
    (chart R (Fin (n + 1)) 0).opensRange_ι

lemma affineChartEmbedding_eq :
    affineChartEmbedding R n =
      Spec.map (CommRingCat.ofHom (chartToPolynomial R n)) ≫
        Proj.awayι (grading R (Fin (n + 1))) (X 0) (isHomogeneous_X R 0) (by decide) :=
  Category.assoc _ _ _

/-- The embedding is a morphism over the original coefficient spectrum. -/
@[reassoc]
lemma affineChartEmbedding_baseProjection :
    affineChartEmbedding R n ≫ baseProjection R (Fin (n + 1)) =
      Spec.map (CommRingCat.ofHom (C : R →+* MvPolynomial (Fin n) R)) := by
  rw [affineChartEmbedding_eq, baseProjection, Category.assoc,
    ← Category.assoc (Proj.awayι _ _ _ _) _, Proj.awayι_toSpecZero,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact chartToPolynomial_scalar R n r

end FLT.Mazur.ProjectiveSpace
