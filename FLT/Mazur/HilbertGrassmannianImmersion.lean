/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertComplementCartesian
public import FLT.Mazur.HilbertInjectiveMonomialImageCover
public import FLT.Mazur.CartesianImageChartImmersion

/-!
# The original polynomial Hilbert scheme immerses in its Grassmannian

The full cartesian matching-chart squares, together with the injective
monomial atlas, make the global map a closed immersion into the union of
those target opens. Composing with that open inclusion gives an immersion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
open GrassmannianChart
set_option backward.isDefEq.respectTransparency false
universe u
variable (R I : Type u) [CommRing R] [Finite I] (d : ℕ)
  {κ : Type u} [Fintype κ]
/-- Choose finite bounded monomial indices for the original ambient basis. -/
local instance immersionMonomialFintype : Fintype (BoundedHilbertMonomials I (d + 1)) :=
  Fintype.ofFinite _
variable (hκ : Fintype.card κ = Fintype.card (BoundedHilbertMonomials I (d + 1)) - d)
local notation "b" => boundedPolynomialBasis R I (d + 1)
local notation "F" => hilbertGrassmannianMap R I d b hκ
local notation "C" => injectiveBoundedPolynomialHilbertCover R I d

/-- The actual matching target charts, indexed by the original injective monomial atlas. -/
def hilbertGrassmannianMatchingChart (m : (C).I₀) :
    splitChartScheme R κ d ⟶
      ambientGrassmannianScheme R (MvPolynomial.restrictTotalDegree I R (d + 1)) κ d :=
  ambientGrassmannianChart R (MvPolynomial.restrictTotalDegree I R (d + 1)) κ d
    (hilbertReindexedAmbient R I d m.val m.property
      (hilbertComplementIndexEquiv I d m.val m.property hκ))

instance hilbertGrassmannianMatchingChart_isOpenImmersion (m : (C).I₀) :
    IsOpenImmersion (hilbertGrassmannianMatchingChart R I d hκ m) :=
  inferInstanceAs (IsOpenImmersion (ambientGrassmannianChart _ _ _ _ _))

/-- These specific target charts cover the image of every original Hilbert point. -/
theorem hilbertGrassmannianMatchingChart_covers (x : polynomialHilbertScheme R I d) :
    ∃ m : (C).I₀, F x ∈ Set.range (hilbertGrassmannianMatchingChart R I d hκ m) := by
  obtain ⟨m, y, hy⟩ := (C).exists_eq x
  let e := hilbertComplementIndexEquiv I d m.val m.property hκ
  refine ⟨m, hilbertReindexedChartMap R I d m.val e y, ?_⟩
  rw [← hy]
  exact congrArg (fun k ↦ k y)
    (hilbertReindexedChartMap_global R I d m.val b hκ m.property e)

/-- The Grassmannian open neighborhood is the union of the actual matching chart images. -/
def hilbertGrassmannianImageNeighborhood :=
  openImageUnion (hilbertGrassmannianMatchingChart R I d hκ)

/-- The original Hilbert morphism factors into that actual open neighborhood. -/
def hilbertGrassmannianImageFactor :
    polynomialHilbertScheme R I d ⟶ (hilbertGrassmannianImageNeighborhood R I d hκ).toScheme :=
  imageChartFactor F (hilbertGrassmannianMatchingChart R I d hκ)
    (hilbertGrassmannianMatchingChart_covers R I d hκ)

/-- Inclusion of the open neighborhood recovers the original global morphism. -/
theorem hilbertGrassmannianImageFactor_ι :
    hilbertGrassmannianImageFactor R I d hκ ≫
      (hilbertGrassmannianImageNeighborhood R I d hκ).ι = F :=
  imageChartFactor_ι _ _ _

/-- Full cartesian chart recovery proves closedness inside the actual open neighborhood. -/
instance hilbertGrassmannianImageFactor_isClosedImmersion :
    IsClosedImmersion (hilbertGrassmannianImageFactor R I d hκ) := by
  apply imageChartFactor_isClosedImmersion F (hilbertGrassmannianMatchingChart R I d hκ)
    (hilbertGrassmannianMatchingChart_covers R I d hκ) (C).X (C).f
    (fun m ↦ hilbertReindexedChartMap R I d m.val
      (hilbertComplementIndexEquiv I d m.val m.property hκ))
  · intro m
    exact hilbertComplement_isPullback R I d m.val b hκ m.property
      (hilbertComplementIndexEquiv I d m.val m.property hκ)
  · intro m
    infer_instance

/-- The global map retaining every original polynomial relation is an actual immersion. -/
instance hilbertGrassmannianMap_isImmersion : IsImmersion F := by
  rw [← hilbertGrassmannianImageFactor_ι R I d hκ]
  infer_instance

end FLT.Mazur.HilbertChart
