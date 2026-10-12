/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AllSectionsHilbertGrassmannianImmersion
public import FLT.Mazur.VariableHilbertCommonAmbientEnvelope

/-!
# A finite Grassmannian product for the original common ambient

A canonical finite complement index removes any extra choice of Grassmannian
rank. The product map retains the whole independent translation scheme and is
an immersion by base change of the actual all-sections Hilbert immersion.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
open GrassmannianChart
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  [LocallyOfFiniteType f] (d : ℕ) (U : X.affineOpens)

/-- The complementary rank is computed from the same finite ambient polynomial module. -/
abbrev commonAmbientGrassmannianIndex :=
  Fin (Nat.card (BoundedHilbertMonomials (AffineOpenFiniteVars f U) (d + 1)) - d)

/-- The actual finite Grassmannian as a scheme over the original coefficient ring. -/
def commonAmbientGrassmannianTest : Over (Spec (.of R)) :=
  Over.mk (ambientGrassmannianStructure R
    (MvPolynomial.restrictTotalDegree (AffineOpenFiniteVars f U) R (d + 1))
    (commonAmbientGrassmannianIndex f d U) d)

/-- Immerse the original all-sections Hilbert chart over its original coefficient base. -/
def commonAmbientGrassmannianArrow :
    commonAmbientHilbertTest f d U ⟶ commonAmbientGrassmannianTest f d U :=
  Over.homMk (allSectionsHilbertGrassmannianMap f d U
    (κ := commonAmbientGrassmannianIndex f d U)
    (by
      let _ := Fintype.ofFinite
        (BoundedHilbertMonomials (AffineOpenFiniteVars f U) (d + 1))
      simp only [commonAmbientGrassmannianIndex, Fintype.card_fin,
      Nat.card_eq_fintype_card]))
    (allSectionsHilbertGrassmannianMap_over f d U _)

instance commonAmbientGrassmannianArrow_isImmersion :
    IsImmersion (commonAmbientGrassmannianArrow f d U).left :=
  inferInstanceAs (IsImmersion (allSectionsHilbertGrassmannianMap f d U _))

variable (V : Over (Spec (.of R)))

/-- Base change keeps the entire original translation scheme, without a finiteness assumption. -/
def commonAmbientGrassmannianProduct :
    prod (commonAmbientHilbertTest f d U) V ⟶
      prod (commonAmbientGrassmannianTest f d U) V :=
  prod.map (commonAmbientGrassmannianArrow f d U) (𝟙 V)

/-- The product is genuinely cartesian over the Hilbert Grassmannian immersion. -/
theorem commonAmbientGrassmannianProduct_isPullback :
    IsPullback (prod.fst : prod (commonAmbientHilbertTest f d U) V ⟶ _).left
      (commonAmbientGrassmannianProduct f d U V).left
      (commonAmbientGrassmannianArrow f d U).left
      (prod.fst : prod (commonAmbientGrassmannianTest f d U) V ⟶ _).left :=
  (IsPullback.of_prod_fst_with_id (commonAmbientGrassmannianArrow f d U) V).map
    (Over.forget _)

instance commonAmbientGrassmannianProduct_isImmersion :
    IsImmersion (commonAmbientGrassmannianProduct f d U V).left :=
  MorphismProperty.of_isPullback (commonAmbientGrassmannianProduct_isPullback f d U V)
    (inferInstanceAs (IsImmersion (commonAmbientGrassmannianArrow f d U).left))

/-- The first product coordinate is the unchanged finite Grassmannian parameter. -/
@[reassoc]
theorem commonAmbientGrassmannianProduct_fst :
    commonAmbientGrassmannianProduct f d U V ≫ prod.fst =
      prod.fst ≫ commonAmbientGrassmannianArrow f d U := prod.map_fst _ _

/-- The independent translation point is unchanged. -/
@[reassoc]
theorem commonAmbientGrassmannianProduct_snd :
    commonAmbientGrassmannianProduct f d U V ≫ prod.snd = prod.snd := by
  simp only [commonAmbientGrassmannianProduct, prod.map_snd, Category.comp_id]

end FLT.Mazur.HilbertChart
