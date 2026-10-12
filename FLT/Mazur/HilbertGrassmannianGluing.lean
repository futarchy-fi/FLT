/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertGrassmannianOverlap

/-!
# The global Hilbert-to-Grassmannian morphism

Glue the full universal ideal's local Grassmannian maps on the actual
Hilbert scheme. Compatibility is proved on categorical intersections,
and the resulting morphism lies over the original coefficient spectrum.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
open GrassmannianChart
set_option backward.isDefEq.respectTransparency false
universe u
variable (R I : Type u) [CommRing R] (d : ℕ)
variable {ι κ : Type u} [Fintype ι] [Fintype κ]
  (b : Module.Basis ι R (MvPolynomial.restrictTotalDegree I R (d + 1)))
  (hκ : Fintype.card κ = Fintype.card ι - d)
local notation "H" => polynomialHilbertScheme R I d
local notation "G" =>
  ambientGrassmannianScheme R (MvPolynomial.restrictTotalDegree I R (d + 1)) κ d

/-- The actual Grassmannian parameter on each affine chart of the Hilbert scheme. -/
def hilbertGrassmannianCoverMap (i : (H).affineOpenCover.I₀) :
    Spec ((H).affineOpenCover.X i) ⟶ G := by
  let _ := polynomialCoverAlgebra R (polynomialHilbertStructure R I d) i
  exact hilbertAffineGrassmannianMap R I d b hκ ((H).affineOpenCover.X i)
    ((H).affineOpenCover.f i)
    (polynomialCoverAlgebra_over R (polynomialHilbertStructure R I d) i)

/-- Local Grassmannian parameters agree on the full categorical Hilbert intersections. -/
theorem hilbertGrassmannianCoverMap_agree (i j : (H).affineOpenCover.I₀) :
    pullback.fst ((H).affineOpenCover.f i) ((H).affineOpenCover.f j) ≫
        hilbertGrassmannianCoverMap R I d b hκ i =
      pullback.snd ((H).affineOpenCover.f i) ((H).affineOpenCover.f j) ≫
        hilbertGrassmannianCoverMap R I d b hκ j := by
  let _ := polynomialCoverAlgebra R (polynomialHilbertStructure R I d) i
  let _ := polynomialCoverAlgebra R (polynomialHilbertStructure R I d) j
  exact hilbertAffineGrassmannianMap_agree R I d b hκ
    ((H).affineOpenCover.X i) ((H).affineOpenCover.X j)
    ((H).affineOpenCover.f i)
    (polynomialCoverAlgebra_over R (polynomialHilbertStructure R I d) i)
    ((H).affineOpenCover.f j)
    (polynomialCoverAlgebra_over R (polynomialHilbertStructure R I d) j)
    _ _ pullback.condition

/-- The morphism from the original Hilbert scheme classifying its full universal quotient. -/
def hilbertGrassmannianMap : H ⟶ G :=
  (H).affineOpenCover.openCover.glueMorphisms
    (hilbertGrassmannianCoverMap R I d b hκ)
    (hilbertGrassmannianCoverMap_agree R I d b hκ)

/-- The global morphism restricts to the original affine quotient classifying maps. -/
@[reassoc] theorem hilbertGrassmannianMap_restrict (i : (H).affineOpenCover.I₀) :
    (H).affineOpenCover.f i ≫ hilbertGrassmannianMap R I d b hκ =
      hilbertGrassmannianCoverMap R I d b hκ i :=
  (H).affineOpenCover.openCover.ι_glueMorphisms _ _ i

/-- The constructed Hilbert-to-Grassmannian morphism preserves the original base map. -/
@[reassoc] theorem hilbertGrassmannianMap_over :
    hilbertGrassmannianMap R I d b hκ ≫
      ambientGrassmannianStructure R (MvPolynomial.restrictTotalDegree I R (d + 1)) κ d =
      polynomialHilbertStructure R I d := by
  apply Scheme.Cover.hom_ext (H).affineOpenCover.openCover
  intro i
  change (H).affineOpenCover.f i ≫ (hilbertGrassmannianMap R I d b hκ ≫ _) =
    (H).affineOpenCover.f i ≫ polynomialHilbertStructure R I d
  rw [← Category.assoc, hilbertGrassmannianMap_restrict]
  let _ := polynomialCoverAlgebra R (polynomialHilbertStructure R I d) i
  exact (hilbertAffineGrassmannianMap_over R I d b hκ ((H).affineOpenCover.X i)
    ((H).affineOpenCover.f i)
    (polynomialCoverAlgebra_over R (polynomialHilbertStructure R I d) i)).trans
      (polynomialCoverAlgebra_over R (polynomialHilbertStructure R I d) i).symm

end FLT.Mazur.HilbertChart
