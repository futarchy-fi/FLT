/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertUniversalComplementMatrix
public import FLT.Mazur.HilbertGrassmannianIdentityChart

/-!
# The closed complementary chart classifies the original Hilbert relation

The affine Grassmannian representation sends the actual closed coordinate map
to the entire bounded relation of the original universal Hilbert family.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
open GrassmannianChart
set_option backward.isDefEq.respectTransparency false
universe u
variable (R I : Type u) [CommRing R] (d : ℕ)
  (m : Fin d → BoundedHilbertMonomials I d)
  {κ : Type u} [Fintype κ] (hm : Function.Injective m)
  (e : HilbertComplementMonomials I d m ≃ κ)
local notation "w" => (fun a ↦ MvPolynomial.monomial (Subtype.val (m a)) (1 : R))
local notation "C" => ChartRing R I d w
local notation "J" => chartIdentityIdeal R I d w
local notation "v" => chartIdentityBasis R I d w
local notation "c" => hilbertReindexedAmbient R I d m hm e
local notation "q" => hilbertAmbientCoordinates R C I J d v
local notation "hd" => chartIdentityIdeal_residueRank R I d w

/-- Cache the original coefficient quotient. -/
local instance complementPointCoefficientsRing : CommRing (Coefficients R I d) := inferInstance
/-- Cache the original chart ring. -/
local instance complementPointChartRing : CommRing C := inferInstance
/-- Cache the original universal quotient. -/
local instance complementPointQuotientRing : CommRing (MvPolynomial I C ⧸ J) := inferInstance

/-- The matrix parameter represents exactly the full original bounded Hilbert relation. -/
theorem hilbertComplementMatrix_point :
    let _ := Classical.decEq κ
    (ambientPointOfCoordinates c (Matrix.toLin' (matrixPolynomialHomEquiv R C κ d
      (chartReindexedCoordinateMap R I d m e)))).val =
        finiteFlatHilbertAmbientPoint R C I J d hd := by
  classical
  dsimp only
  rw [← chartIdentityCoordinates_complement R I d m hm e]
  exact normalizedAmbientCoordinates_point _ q
    (chartIdentityCoordinates_selected R I d m hm e) _
    (hilbertAmbientCoordinates_kernel R C I J d v hd)

/-- The actual closed scheme map classifies that same full original quotient point. -/
theorem hilbertReindexedChartMap_point :
    (ambientChartSchemePointEquiv c
      ⟨hilbertReindexedChartMap R I d m e, hilbertReindexedChartMap_over R I d m e⟩).val =
        finiteFlatHilbertAmbientPoint R C I J d hd := by
  classical
  have h := ambientChartSchemePointEquiv_ofAlgHom c (chartReindexedCoordinateMap R I d m e)
  exact (congrArg Subtype.val h).trans (hilbertComplementMatrix_point R I d m hm e)

end FLT.Mazur.HilbertChart
