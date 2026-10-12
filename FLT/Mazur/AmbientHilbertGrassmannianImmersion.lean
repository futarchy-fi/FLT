/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertGrassmannianImmersion
public import FLT.Mazur.HilbertAmbientClosedParameter

/-!
# Grassmannian immersion retaining every original ambient equation

The actual closed ambient Hilbert parameter scheme inherits the constructed
Grassmannian immersion. Its factor into the matching target neighborhood is
closed and still imposes the entire original ambient ideal, without assuming
that ideal is finitely generated or that the parameter scheme is affine.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
open GrassmannianChart
set_option backward.isDefEq.respectTransparency false
universe u
variable (R I : Type u) [CommRing R] [Finite I] (d : ℕ)
  (K : Ideal (MvPolynomial I R)) {κ : Type u} [Fintype κ]
/-- Use the same original bounded monomial basis as the polynomial immersion. -/
local instance ambientImmersionMonomialFintype :
    Fintype (BoundedHilbertMonomials I (d + 1)) := Fintype.ofFinite _
variable (hκ : Fintype.card κ = Fintype.card (BoundedHilbertMonomials I (d + 1)) - d)

/-- The actual ambient Hilbert parameter map into the original Grassmannian. -/
def ambientHilbertGrassmannianMap : ambientHilbertScheme R I d K ⟶
    ambientGrassmannianScheme R (MvPolynomial.restrictTotalDegree I R (d + 1)) κ d :=
  ambientHilbertι R I d K ≫
    hilbertGrassmannianMap R I d (boundedPolynomialBasis R I (d + 1)) hκ

/-- The ambient map preserves its original coefficient structure. -/
theorem ambientHilbertGrassmannianMap_over :
    ambientHilbertGrassmannianMap R I d K hκ ≫
      ambientGrassmannianStructure R (MvPolynomial.restrictTotalDegree I R (d + 1)) κ d =
        ambientHilbertStructure R I d K := by
  rw [ambientHilbertGrassmannianMap, Category.assoc, hilbertGrassmannianMap_over]
  rfl

/-- The whole ambient parameter scheme is closed in the actual matching target neighborhood. -/
def ambientHilbertGrassmannianImageFactor : ambientHilbertScheme R I d K ⟶
    (hilbertGrassmannianImageNeighborhood R I d hκ).toScheme :=
  ambientHilbertι R I d K ≫ hilbertGrassmannianImageFactor R I d hκ

instance ambientHilbertGrassmannianImageFactor_isClosedImmersion :
    IsClosedImmersion (ambientHilbertGrassmannianImageFactor R I d K hκ) :=
  inferInstanceAs (IsClosedImmersion
    (ambientHilbertι R I d K ≫ hilbertGrassmannianImageFactor R I d hκ))

/-- Including the target neighborhood recovers the unchanged ambient parameter map. -/
theorem ambientHilbertGrassmannianImageFactor_ι :
    ambientHilbertGrassmannianImageFactor R I d K hκ ≫
      (hilbertGrassmannianImageNeighborhood R I d hκ).ι =
        ambientHilbertGrassmannianMap R I d K hκ := by
  rw [ambientHilbertGrassmannianImageFactor, Category.assoc, hilbertGrassmannianImageFactor_ι]
  rfl

/-- The genuine ambient Hilbert scheme is immersed with every original relation retained. -/
instance ambientHilbertGrassmannianMap_isImmersion :
    IsImmersion (ambientHilbertGrassmannianMap R I d K hκ) := by
  rw [← ambientHilbertGrassmannianImageFactor_ι R I d K hκ]
  infer_instance

end FLT.Mazur.HilbertChart
