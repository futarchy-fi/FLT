/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingBoundaryLift
public import FLT.Mazur.PolygonSmoothingRingMapBranch

/-!
# Full branch squares of the constructed node extension

Use the two original punctures, with no inversion of the right-hand source.
The inverse coordinate appears only inside the coefficient test needed to
construct the map. The resulting scheme morphism preserves the original base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (t : R)
  (f g : ChartRing t →ₐ[R] R[T;T⁻¹])
  (hx : LaurentCompatible t (f (leftCoordinate t))
    (LaurentPolynomial.invert (g (leftCoordinate t))))
  (hy : LaurentCompatible t (f (rightCoordinate t))
    (LaurentPolynomial.invert (g (rightCoordinate t))))

/-- Construct the node map while retaining the two original puncture orientations. -/
def twoBranchLift : ChartRing t →ₐ[R] ChartRing t :=
  boundaryLift t t f (LaurentPolynomial.invert.toAlgHom.comp g) hx hy

/-- Its full outgoing restriction is exactly the given outgoing algebra map. -/
theorem twoBranchLift_left : (leftLaurentMap t).comp (twoBranchLift t f g hx hy) = f :=
  leftLaurentMap_boundaryLift t t f
    (LaurentPolynomial.invert.toAlgHom.comp g) hx hy

/-- Its full incoming restriction has the original, uninverted branch coordinate. -/
theorem twoBranchLift_right :
    ((leftLaurentMap t).comp (branchSwapMap t)).comp (twoBranchLift t f g hx hy) = g := by
  apply AlgHom.ext
  intro z
  apply LaurentPolynomial.invert.injective
  exact DFunLike.congr_fun (precedingLaurentMap_boundaryLift t t f
    (LaurentPolynomial.invert.toAlgHom.comp g) hx hy) z

/-- The constructed map of the entire original node chart. -/
def twoBranchLiftMap : chart R t ⟶ chart R t :=
  Spec.map (CommRingCat.ofHom (twoBranchLift t f g hx hy).toRingHom)

/-- The whole outgoing puncture square commutes, with all original Laurent coefficients. -/
@[reassoc] theorem twoBranchLiftMap_left :
    leftBranchOpen R t ≫ twoBranchLiftMap t f g hx hy =
      Spec.map (CommRingCat.ofHom f.toRingHom) := by
  rw [leftBranchOpen_eq_spec, twoBranchLiftMap, ← Spec.map_comp]
  exact congrArg Spec.map
    (CommRingCat.hom_ext (congrArg AlgHom.toRingHom (twoBranchLift_left t f g hx hy)))

/-- The same whole-node map gives the full second puncture square. -/
@[reassoc] theorem twoBranchLiftMap_right :
    rightBranchOpen R t ≫ twoBranchLiftMap t f g hx hy =
      Spec.map (CommRingCat.ofHom g.toRingHom) := by
  rw [rightBranchOpen_eq_spec, twoBranchLiftMap, ← Spec.map_comp]
  exact congrArg Spec.map
    (CommRingCat.hom_ext (congrArg AlgHom.toRingHom (twoBranchLift_right t f g hx hy)))

/-- The complete extension preserves the original nonreduced coefficient base. -/
@[reassoc] theorem twoBranchLiftMap_base :
    twoBranchLiftMap t f g hx hy ≫ chartStructure R t = chartStructure R t := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (twoBranchLift t f g hx hy).comp_algebraMap)

/-- A full extension with the prescribed two original punctures is unique. -/
theorem twoBranchLift_unique (F : ChartRing t →ₐ[R] ChartRing t)
    (hl : (leftLaurentMap t).comp F = f)
    (hr : ((leftLaurentMap t).comp (branchSwapMap t)).comp F = g) :
    F = twoBranchLift t f g hx hy := by
  apply boundaryLift_unique t t f (LaurentPolynomial.invert.toAlgHom.comp g) hx hy F hl
  exact congrArg (LaurentPolynomial.invert.toAlgHom.comp) hr

end FLT.Mazur.PolygonSmoothing
