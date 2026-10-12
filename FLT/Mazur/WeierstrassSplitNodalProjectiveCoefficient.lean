/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalLaurentCoefficient
public import FLT.Mazur.WeierstrassSplitNodalProjectiveReflection
public import FLT.Mazur.AffineSectionLineCoefficientMap

/-!
# Specialization of the full projective nodal torus parameter

The comparison is an equality of scheme morphisms on the entire Laurent
scheme, including the identity and all nonreduced coefficient rings.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) (a : Sˣ)
variable (b : Tˣ) (hb : Units.map f a = b)
local notation "L" => nodalLaurentCoefficientMap f
local notation "P" => (![splitNodalLaurentX a, 1, splitNodalLaurentZ a] : Fin 3 → S[T;T⁻¹])
local notation "Q" => (![splitNodalLaurentX b, 1, splitNodalLaurentZ b] : Fin 3 → T[T;T⁻¹])

include hb in
/-- The normalized homogeneous tuple specializes coordinate by coordinate. -/
theorem splitNodalLaurentTuple_coefficient : (fun i => L (P i)) = Q := by
  subst b
  funext i
  fin_cases i
  · exact splitNodalLaurentX_coefficient f a
  · exact map_one _
  · exact splitNodalLaurentZ_coefficient f a

include hb in
/-- The whole original projective torus map commutes with every coefficient homomorphism. -/
@[reassoc] theorem splitNodalTorus_projectiveCoefficient :
    Spec.map (CommRingCat.ofHom L) ≫ splitNodalTorusToCurve a ≫
        integralProjectiveMap (splitNodalEquation a) =
      splitNodalTorusToCurve (R := T) b ≫
        integralProjectiveMap (R := T) (splitNodalEquation (R := T) b) ≫
        ProjectiveSpace.coefficientMap f (Fin 3) := by
  rw [splitNodalTorus_projectivePoint, splitNodalTorus_projectivePoint_assoc,
    ProjectiveSpace.unitChartPoint_map, ProjectiveSpace.unitChartPoint_coefficientMap]
  have hc : (L).comp (algebraMap S S[T;T⁻¹]) = (algebraMap T T[T;T⁻¹]).comp f := by
    exact RingHom.ext (nodalLaurentCoefficientMap_scalar f)
  simp only [hc, splitNodalLaurentTuple_coefficient f a b hb, map_one]

/-- The full Laurent coefficient map has the prescribed coefficient-spectrum structure. -/
@[reassoc] theorem nodalLaurentCoefficientMap_structure :
    Spec.map (CommRingCat.ofHom L) ≫ (MultiplicativeGroupScheme.gm S).hom =
      (MultiplicativeGroupScheme.gm T).hom ≫ Spec.map (CommRingCat.ofHom f) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (nodalLaurentCoefficientMap_scalar f))

end FLT.Mazur.WeierstrassIntegralChart
