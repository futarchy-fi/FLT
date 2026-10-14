/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalUniversalScaling

/-!
# Coefficient naturality of the variable whole-polygon action

The parameter remains a variable Laurent coordinate under arbitrary base
change. The full source, its projection, and its polygon-valued scaling map
commute with the original coefficient maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
universe u
namespace FLT.Mazur.PolygonInfinitesimal
set_option backward.isDefEq.respectTransparency false
variable {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S) (t : R) (s : S) [Fact (IsNilpotent t)] [Fact (IsNilpotent s)]
  (hs : f t = s) (n : ℕ) (h : 2 ≤ n)

/-- Change original coefficients while retaining the independent Laurent action parameter. -/
def scalingParameterMap : scalingParameterFamily S s n h ⟶ scalingParameterFamily R t n h :=
  parameterProjection (PolygonScalingNaturality.coeffMap f)
    (LaurentPolynomial.C t) (LaurentPolynomial.C s) (by simp [hs]) n h

/-- The full source comparison retains the actual Laurent coefficient map. -/
@[reassoc] theorem scalingParameterMap_base :
    scalingParameterMap f t s hs n h ≫ toBase R[T;T⁻¹] (LaurentPolynomial.C t) n h =
      toBase S[T;T⁻¹] (LaurentPolynomial.C s) n h ≫
        Spec.map (CommRingCat.ofHom (PolygonScalingNaturality.coeffMap f)) :=
  parameterProjection_base _ _ _ _ _ _

/-- Forgetting the parameter commutes with the original full-polygon coefficient change. -/
@[reassoc] theorem scalingParameterMap_projection :
    scalingParameterMap f t s hs n h ≫ scalingParameterProjection R t n h =
      scalingParameterProjection S s n h ≫ parameterProjection f t s hs n h := by
  simp only [scalingParameterMap, scalingParameterProjection, parameterProjection_comp]
  congr 1
  ext r
  simp

/-- Variable scaling commutes with arbitrary original coefficients, including nilpotents. -/
@[reassoc] theorem scalingParameterMap_universalScaling :
    scalingParameterMap f t s hs n h ≫ universalScaling R t n h =
      universalScaling S s n h ≫ parameterProjection f t s hs n h := by
  have hu : Units.map (PolygonScalingNaturality.coeffMap f)
      (PolygonUniversalScaling.u (R := R)) = PolygonUniversalScaling.u (R := S) := by
    ext
    simp [PolygonUniversalScaling.u, PolygonChartScaling.coordinateUnit]
  have he := (scaling_parameterProjection (PolygonScalingNaturality.coeffMap f)
    (LaurentPolynomial.C t) (LaurentPolynomial.C s) (by simp [hs]) n h
    (PolygonUniversalScaling.u (R := R))).symm
  rw [hu] at he
  change scalingParameterMap f t s hs n h ≫ _ =
    scaling S[T;T⁻¹] (LaurentPolynomial.C s) n h _ ≫ scalingParameterMap f t s hs n h at he
  rw [universalScaling, ← Category.assoc, he, Category.assoc,
    scalingParameterMap_projection, universalScaling, Category.assoc]

end FLT.Mazur.PolygonInfinitesimal
