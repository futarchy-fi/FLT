/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianDeterminantAmple
public import FLT.Mazur.CommonAmbientAmpleFiniteNeighborhood
public import FLT.Mazur.AmpleAffinePullback

/-!
# The actual determinant line on the common-ambient product target

The original finite monomial basis proves Grassmannian determinant ampleness.
Pullback along the affine first projection gives an actual ample line on the
product with the entire affine translation scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.HilbertChart
open GrassmannianChart FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  [LocallyOfFiniteType f] (d : ℕ) (U : X.affineOpens)

/-- The concrete determinant line on the original finite Grassmannian target. -/
@[irreducible] def commonAmbientGrassmannianLine :
    (commonAmbientGrassmannianTest f d U).left.Modules :=
  determinantLine R (MvPolynomial.restrictTotalDegree (AffineOpenFiniteVars f U) R (d + 1))
    (commonAmbientGrassmannianIndex f d U) d

/-- The line on the common ambient Grassmannian is actually locally free of rank one. -/
theorem commonAmbientGrassmannianLine_rankOne :
    LocallyFreeRankOne (commonAmbientGrassmannianLine f d U) := by
  delta commonAmbientGrassmannianLine
  exact determinantLine_locallyFreeRankOne _ _ _ _

/-- The original finite monomial basis proves ampleness of the actual Grassmannian line. -/
theorem commonAmbientGrassmannianLine_ample :
    AmpleLineBundle (commonAmbientGrassmannianLine f d U) := by
  let _ := Fintype.ofFinite (BoundedHilbertMonomials (AffineOpenFiniteVars f U) (d + 1))
  delta commonAmbientGrassmannianLine
  apply determinantLine_ample (boundedPolynomialBasis R (AffineOpenFiniteVars f U) (d + 1))
  simp only [commonAmbientGrassmannianIndex, Fintype.card_fin, Nat.card_eq_fintype_card]

variable (V : Over (Spec (.of R)))

/-- The constructed determinant candidate on the product with the entire translation scheme. -/
@[irreducible] def commonAmbientTargetDeterminantLine :
    (prod (commonAmbientGrassmannianTest f d U) V).left.Modules :=
  (Scheme.Modules.pullback (prod.fst : prod (commonAmbientGrassmannianTest f d U) V ⟶ _).left).obj
    (commonAmbientGrassmannianLine f d U)

/-- Arbitrary translation schemes retain an actual line bundle on the target product. -/
theorem commonAmbientTargetDeterminantLine_rankOne :
    LocallyFreeRankOne (commonAmbientTargetDeterminantLine f d U V) := by
  delta commonAmbientTargetDeterminantLine
  exact (commonAmbientGrassmannianLine_rankOne f d U).pullback _

/-- Affine translation makes the original first product projection affine. -/
instance commonAmbientTargetProjection_isAffine [IsAffine V.left] :
    IsAffineHom (prod.fst : prod (commonAmbientGrassmannianTest f d U) V ⟶ _).left := by
  have hp := Over.isPullback_of_binaryFan_isLimit _
    (prodIsProd (commonAmbientGrassmannianTest f d U) V)
  exact MorphismProperty.of_isPullback hp.flip (inferInstanceAs (IsAffineHom V.hom))

/-- The constructed line is ample on the product with the whole affine translation scheme. -/
theorem commonAmbientTargetDeterminantLine_ample [IsAffine V.left] :
    AmpleLineBundle (commonAmbientTargetDeterminantLine f d U V) := by
  delta commonAmbientTargetDeterminantLine
  exact (commonAmbientGrassmannianLine_ample f d U).pullback_affine _

end FLT.Mazur.HilbertChart
