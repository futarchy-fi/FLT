/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.LaurentUnitMultiplication
public import FLT.Mazur.WeierstrassSplitNodalSmoothGroup

/-!
# Coordinates of the full smooth group multiplication

The categorical multiplication on the entire relative smooth locus evaluates
at the product of the input Laurent coordinates on arbitrary source schemes.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CartesianMonoidalCategory MonObj

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (s : X ⟶ Spec (.of R))

/-- Categorical torus multiplication multiplies the units of arbitrary scheme-valued inputs. -/
theorem laurentUnit_over_multiplication
    (p q : Over.mk s ⟶ MultiplicativeGroupScheme.gm R) :
    let _ := specSectionAlgebra s
    let P := specSectionAlgHom s p.left p.w
    let Q := specSectionAlgHom s q.left q.w
    (lift p q ≫ μ[MultiplicativeGroupScheme.gm R]).left =
      specSectionMorphism (LaurentUnitPoints.evalUnit (R := R)
        (LaurentUnitPoints.pointUnit P * LaurentUnitPoints.pointUnit Q)).toRingHom := by
  let _ := specSectionAlgebra s
  let P := specSectionAlgHom s p.left p.w
  let Q := specSectionAlgHom s q.left q.w
  have hp : specSectionMorphism
      (LaurentUnitPoints.evalUnit (LaurentUnitPoints.pointUnit P)).toRingHom = p.left := by
    rw [LaurentUnitPoints.evalUnit_pointUnit]
    exact specSectionMorphism_hom p.left
  have hq : specSectionMorphism
      (LaurentUnitPoints.evalUnit (LaurentUnitPoints.pointUnit Q)).toRingHom = q.left := by
    rw [LaurentUnitPoints.evalUnit_pointUnit]
    exact specSectionMorphism_hom q.left
  have h := laurentUnit_scheme_multiplication (R := R)
    (LaurentUnitPoints.pointUnit P) (LaurentUnitPoints.pointUnit Q)
    (by rw [hp, hq]; exact p.w.trans q.w.symm)
  simp only [hp, hq] at h
  exact h

variable (a : Rˣ)

/-- Transport of multiplication commutes with pairing arbitrary smooth-locus inputs. -/
theorem splitNodalSmooth_multiplication_transport
    (p q : Over.mk s ⟶ splitNodalSmoothOver a) :
    let _ := splitNodalSmoothCommGrpObj a
    lift p q ≫ μ[splitNodalSmoothOver a] =
      lift (p ≫ (splitNodalRelativeSmoothOverIso a).inv)
          (q ≫ (splitNodalRelativeSmoothOverIso a).inv) ≫
        μ[MultiplicativeGroupScheme.gm R] ≫ (splitNodalRelativeSmoothOverIso a).hom := by
  let _ := splitNodalSmoothCommGrpObj a
  dsimp only
  rw [splitNodalSmoothGroup_multiplication, ← Category.assoc, ← Category.assoc,
    lift_map, Category.assoc]

/-- The actual full smooth multiplication has product-unit coordinates in the original cubic. -/
theorem splitNodalSmooth_multiplication_coordinates
    (p q : Over.mk s ⟶ splitNodalSmoothOver a) :
    let _ := specSectionAlgebra s
    let _ := splitNodalSmoothCommGrpObj a
    let P := specSectionAlgHom s
      (p ≫ (splitNodalRelativeSmoothOverIso a).inv).left
      (p ≫ (splitNodalRelativeSmoothOverIso a).inv).w
    let Q := specSectionAlgHom s
      (q ≫ (splitNodalRelativeSmoothOverIso a).inv).left
      (q ≫ (splitNodalRelativeSmoothOverIso a).inv).w
    (lift p q ≫ μ[splitNodalSmoothOver a]).left ≫
        (integralSmoothOpen (splitNodalEquation a)).ι =
      specSectionMorphism (LaurentUnitPoints.evalUnit (R := R)
        (LaurentUnitPoints.pointUnit P * LaurentUnitPoints.pointUnit Q)).toRingHom ≫
          splitNodalTorusToCurve a := by
  let _ := specSectionAlgebra s
  let _ := splitNodalSmoothCommGrpObj a
  dsimp only
  rw [splitNodalSmooth_multiplication_transport]
  change ((lift _ _ ≫ μ[MultiplicativeGroupScheme.gm R]).left ≫
    splitNodalTorusToSmooth a) ≫ _ = _
  rw [Category.assoc, splitNodalTorusToSmooth_inclusion, laurentUnit_over_multiplication]

end FLT.Mazur.WeierstrassIntegralChart
