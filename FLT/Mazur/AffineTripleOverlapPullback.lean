/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineGeometricOverlap
public import FLT.Mazur.AffineIteratedPullbackLaws

/-!
# Actual triple-overlap sheaf comparisons

The three pair pullbacks of an overlap map are normalized to maps between
the actual coordinate pullback sheaves. Their effect on coefficient sections
is determined by the adjunction units, and the geometric cocycle is an
equality between these sheaf morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineTripleOverlapPullback
open AffineOverlapTensor AffineOverlapPullback AffineTripleOverlapMaps
open AffineIteratedPullbackSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (M : (Spec (.of S)).Modules)
/-- Coefficient scalars restricted to the base ring. -/
local instance coefficientModule : Module R (coefficients S M) := Module.compHom _ (algebraMap R S)
local instance : IsScalarTower R S (coefficients S M) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)

/-- The coordinate pullback associated to a ring inclusion. -/
abbrev coordinate (j : S →+* Triple R S) :=
  (pullback (Spec.map (CommRingCat.ofHom j))).obj M

/-- The direct unit section in a coordinate pullback. -/
abbrev unitSection (j : S →+* Triple R S) (n : coefficients S M) :
    moduleSpecΓFunctor.obj (coordinate R S M j) :=
  specUnit (CommRingCat.ofHom j) M n

/-- Normalize the pullback of the overlap along a pair projection. -/
def transport (p : S ⊗[R] S →ₐ[R] Triple R S) (i j : S →+* Triple R S)
    (hi : p.toRingHom.comp (left R S) = i) (hj : p.toRingHom.comp (right R S) = j)
    (e : AffineGeometricOverlap.Overlap R S M) :
    coordinate R S M i ≅ coordinate R S M j :=
  (comparison (left R S) p.toRingHom i hi M).symm ≪≫
    (pullback (Spec.map (CommRingCat.ofHom p.toRingHom))).mapIso e ≪≫
      comparison (right R S) p.toRingHom j hj M

/-- Normalize the first pair transport. -/
abbrev transport12 (e : AffineGeometricOverlap.Overlap R S M) :=
  transport R S M (pair12 R S) (coord1 R S) (coord2 R S)
    (pair12_left R S) (pair12_right R S) e

/-- Normalize the last pair transport. -/
abbrev transport23 (e : AffineGeometricOverlap.Overlap R S M) :=
  transport R S M (pair23 R S) (coord2 R S) (coord3 R S)
    (pair23_left R S) (pair23_right R S) e

/-- Normalize the outer pair transport. -/
abbrev transport13 (e : AffineGeometricOverlap.Overlap R S M) :=
  transport R S M (pair13 R S) (coord1 R S) (coord3 R S)
    (pair13_left R S) (pair13_right R S) e

/-- The geometric cocycle uses actual pullback maps and composition comparisons. -/
def CocycleCompatible (e : AffineGeometricOverlap.Overlap R S M) : Prop :=
  (transport12 R S M e).hom ≫ (transport23 R S M e).hom = (transport13 R S M e).hom

/-- The pair transport has the specified conjugated pullback morphism. -/
theorem transport_hom (p : S ⊗[R] S →ₐ[R] Triple R S) (i j : S →+* Triple R S)
    (hi : p.toRingHom.comp (left R S) = i) (hj : p.toRingHom.comp (right R S) = j)
    (e : AffineGeometricOverlap.Overlap R S M) :
    (transport R S M p i j hi hj e).hom =
      (comparison (left R S) p.toRingHom i hi M).inv ≫
        (pullback (Spec.map (CommRingCat.ofHom p.toRingHom))).map e.hom ≫
          (comparison (right R S) p.toRingHom j hj M).hom := rfl

variable [M.IsQuasicoherent]

/-- Normalized pair pullback intertwines the coefficient overlap map. -/
theorem comparison_sections (p : S ⊗[R] S →ₐ[R] Triple R S) (i j : S →+* Triple R S)
    (hi : p.toRingHom.comp (left R S) = i) (hj : p.toRingHom.comp (right R S) = j)
    (e : AffineGeometricOverlap.Overlap R S M) (x : coefficients S M ⊗[R] S) :
    moduleSpecΓFunctor.map
      ((comparison (left R S) p.toRingHom i hi M).inv ≫
        (pullback (Spec.map (CommRingCat.ofHom p.toRingHom))).map e.hom ≫
          (comparison (right R S) p.toRingHom j hj M).hom)
      (mappedUnit (CommRingCat.ofHom p.toRingHom) _
        (comparison (left R S) p.toRingHom i hi M).hom (firstSections R S M x)) =
      mappedUnit (CommRingCat.ofHom p.toRingHom) _
        (comparison (right R S) p.toRingHom j hj M).hom
        (moduleSpecΓFunctor.map e.hom (firstSections R S M x)) :=
  mappedUnit_map (CommRingCat.ofHom p.toRingHom) _
    (comparison (left R S) p.toRingHom i hi M)
    (comparison (right R S) p.toRingHom j hj M) e.hom (firstSections R S M x)

/-- The actual pair transport is the specified tensor overlap on normalized coefficients. -/
theorem transport_sections (p : S ⊗[R] S →ₐ[R] Triple R S) (i j : S →+* Triple R S)
    (hi : p.toRingHom.comp (left R S) = i) (hj : p.toRingHom.comp (right R S) = j)
    (e : AffineGeometricOverlap.Overlap R S M) (x : coefficients S M ⊗[R] S) :
    moduleSpecΓFunctor.map (transport R S M p i j hi hj e).hom
      (mappedUnit (CommRingCat.ofHom p.toRingHom) _
        (comparison (left R S) p.toRingHom i hi M).hom (firstSections R S M x)) =
      mappedUnit (CommRingCat.ofHom p.toRingHom) _
        (comparison (right R S) p.toRingHom j hj M).hom
        (secondSections R S M (AffineGeometricOverlap.tensorEquiv R S M e x)) := by
  rw [transport_hom, AffineGeometricOverlap.tensorEquiv_sections]
  exact comparison_sections R S M p i j hi hj e x

end FLT.Mazur.AffineTripleOverlapPullback
