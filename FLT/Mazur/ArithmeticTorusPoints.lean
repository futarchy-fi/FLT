/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MultiplicativeGroupScheme
public import FLT.Mazur.LaurentUnitMultiplication
public import FLT.Mazur.AffineProductMap

/-!
# Arithmetic unit sections of the actual multiplicative group

Evaluation at a coefficient unit defines a section over any commutative ring.
These sections respect the categorical group law, including on nonreduced bases.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped LaurentPolynomial

namespace FLT.Mazur.ArithmeticTorusPoints

universe u
variable (R : Type u) [CommRing R]

/-- The actual torus section with the specified invertible Laurent coordinate. -/
def point (a : Rˣ) : 𝟙_ (Over (Spec (.of R))) ⟶ MultiplicativeGroupScheme.gm R :=
  Over.homMk (Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R) a).toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    exact CommRingCat.hom_ext (LaurentUnitPoints.evalUnit a).comp_algebraMap)

/-- Evaluation retains the exact underlying scheme morphism. -/
theorem point_left (a : Rˣ) : (point R a).left =
    Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R) a).toRingHom) := rfl

/-- Multiplication of sections is multiplication of their unit coordinates. -/
theorem point_mul (a b : Rˣ) : point R (a * b) = point R a * point R b := by
  apply Over.OverMorphism.ext
  let hpair := (point R a).w.trans (point R b).w.symm
  change Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R) (a * b)).toRingHom) =
    CategoryTheory.Limits.pullback.lift
      (Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R) a).toRingHom))
      (Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R) b).toRingHom))
      hpair ≫
        μ[MultiplicativeGroupScheme.gm R].left
  rw [MultiplicativeGroupScheme.multiplication_left, ← Category.assoc,
    ← Approximation.affineProductMap_spec]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_assoc]
  rw [← Spec.map_comp]
  exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (WeierstrassIntegralChart.laurentUnit_product_comul (R := R) a b).symm

/-- Units map homomorphically into the actual group of sections over the ring. -/
def pointHom : Rˣ →* (𝟙_ (Over (Spec (.of R))) ⟶ MultiplicativeGroupScheme.gm R) :=
  MonoidHom.mk' (point R) (point_mul R)

/-- Unit powers are the categorical powers of the actual section. -/
theorem point_pow (a : Rˣ) (k : ℕ) : point R (a ^ k) = point R a ^ k :=
  (pointHom R).map_pow a k

/-- The unit identity is the categorical identity section. -/
theorem point_one : point R 1 = 1 := (pointHom R).map_one

end FLT.Mazur.ArithmeticTorusPoints
