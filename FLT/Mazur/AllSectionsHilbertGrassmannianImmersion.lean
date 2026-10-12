/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertFiniteAmbientPresentation
public import FLT.Mazur.AmbientHilbertGrassmannianImmersion

/-!
# Immersing the literal all-sections Hilbert chart

The finite-coordinate comparison transports the genuine Grassmannian immersion
back to the original all-sections chart. Its closed factor retains the entire
original ambient ideal and its original coefficient morphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
open GrassmannianChart
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] {Z : Scheme.{u}} (z : Z ⟶ Spec (.of R))
  [LocallyOfFiniteType z] (d : ℕ) (U : Z.affineOpens) {κ : Type u} [Fintype κ]

/-- Finite monomials come from a presentation of the same original affine ambient. -/
local instance allSectionsImmersionMonomialFintype :
    Fintype (BoundedHilbertMonomials (AffineOpenFiniteVars z U) (d + 1)) :=
  Fintype.ofFinite _
variable (hκ : Fintype.card κ =
  Fintype.card (BoundedHilbertMonomials (AffineOpenFiniteVars z U) (d + 1)) - d)

/-- The original all-sections parameter maps into a finite-coordinate Grassmannian. -/
def allSectionsHilbertGrassmannianMap : (allAffineAmbientCharts z).hilbert d U ⟶
    ambientGrassmannianScheme R
      (MvPolynomial.restrictTotalDegree (AffineOpenFiniteVars z U) R (d + 1)) κ d :=
  (finiteAffineAmbientHilbertIso z d U).inv ≫
    ambientHilbertGrassmannianMap R (AffineOpenFiniteVars z U) d
      (affineOpenFiniteRelations z U) hκ

/-- Finite-coordinate comparison recovers the original constructed finite map. -/
@[reassoc]
theorem allSectionsHilbertGrassmannianMap_comparison :
    (finiteAffineAmbientHilbertIso z d U).hom ≫
      allSectionsHilbertGrassmannianMap z d U hκ =
        ambientHilbertGrassmannianMap R (AffineOpenFiniteVars z U) d
          (affineOpenFiniteRelations z U) hκ := by
  simp only [allSectionsHilbertGrassmannianMap, Iso.hom_inv_id_assoc]

/-- The immersion preserves the coefficient morphism of the literal original chart. -/
@[reassoc]
theorem allSectionsHilbertGrassmannianMap_over :
    allSectionsHilbertGrassmannianMap z d U hκ ≫
      ambientGrassmannianStructure R
        (MvPolynomial.restrictTotalDegree (AffineOpenFiniteVars z U) R (d + 1)) κ d =
      ambientHilbertStructure R Γ(Z, U.val) d (affineOpenRelations z U) := by
  rw [allSectionsHilbertGrassmannianMap, Category.assoc,
    ambientHilbertGrassmannianMap_over, ← finiteAffineAmbientHilbertIso_over z d U,
    Iso.inv_hom_id_assoc]

/-- The literal chart is closed in the same open Grassmannian neighborhood. -/
def allSectionsHilbertGrassmannianImageFactor :
    (allAffineAmbientCharts z).hilbert d U ⟶
      (hilbertGrassmannianImageNeighborhood R (AffineOpenFiniteVars z U) d hκ).toScheme :=
  (finiteAffineAmbientHilbertIso z d U).inv ≫
    ambientHilbertGrassmannianImageFactor R (AffineOpenFiniteVars z U) d
      (affineOpenFiniteRelations z U) hκ

instance allSectionsHilbertGrassmannianImageFactor_isClosedImmersion :
    IsClosedImmersion (allSectionsHilbertGrassmannianImageFactor z d U hκ) := by
  unfold allSectionsHilbertGrassmannianImageFactor
  infer_instance

/-- Including the neighborhood recovers the actual all-sections morphism. -/
@[reassoc]
theorem allSectionsHilbertGrassmannianImageFactor_ι :
    allSectionsHilbertGrassmannianImageFactor z d U hκ ≫
      (hilbertGrassmannianImageNeighborhood R (AffineOpenFiniteVars z U) d hκ).ι =
        allSectionsHilbertGrassmannianMap z d U hκ := by
  rw [allSectionsHilbertGrassmannianImageFactor, Category.assoc,
    ambientHilbertGrassmannianImageFactor_ι]
  rfl

instance allSectionsHilbertGrassmannianMap_isImmersion :
    IsImmersion (allSectionsHilbertGrassmannianMap z d U hκ) := by
  unfold allSectionsHilbertGrassmannianMap
  infer_instance

end FLT.Mazur.HilbertChart
