/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonGroupPoints
public import FLT.Mazur.AffineProductMap
public import FLT.Mazur.LaurentUnitMultiplication

/-!
# The group of actual torus points is the coefficient unit group

The existing unit-point parametrization respects the categorical torus law.
Full faithfulness of Spec and the Laurent coordinate prove its injectivity.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped LaurentPolynomial
namespace FLT.Mazur.TorusPointUnitEquiv

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open PolygonActionTranslation
universe u
variable (K : Type u) [Field K]

/-- Unit-point parametrization detects the original coefficient unit. -/
theorem point_injective : Function.Injective (gmPoint K) := by
  intro a b h
  have he := Spec.map_injective (congrArg (fun z ↦ z.left) h)
  have hx := congrArg (fun z ↦ z.hom (LaurentPolynomial.T 1)) he
  change LaurentPolynomial.eval₂ (RingHom.id K) a (LaurentPolynomial.T 1) =
    LaurentPolynomial.eval₂ (RingHom.id K) b (LaurentPolynomial.T 1) at hx
  apply Units.ext
  simpa only [LaurentPolynomial.eval₂_T, zpow_one] using hx

/-- The actual categorical torus multiplication multiplies the prescribed units. -/
theorem point_mul (a b : Kˣ) : gmPoint K (a * b) = gmPoint K a * gmPoint K b := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := K) (a * b)).toRingHom) =
    CategoryTheory.Limits.pullback.lift
      (Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := K) a).toRingHom))
      (Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := K) b).toRingHom))
      ((gmPoint K a).w.trans (gmPoint K b).w.symm) ≫
        μ[MultiplicativeGroupScheme.gm K].left
  rw [MultiplicativeGroupScheme.multiplication_left, ← Category.assoc,
    ← Approximation.affineProductMap_spec]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_assoc]
  rw [← Spec.map_comp]
  exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (WeierstrassIntegralChart.laurentUnit_product_comul (R := K) a b).symm

/-- Units map homomorphically to the actual relative torus points. -/
def pointHom : Kˣ →* (𝟙_ (Over (Spec (.of K))) ⟶ MultiplicativeGroupScheme.gm K) :=
  MonoidHom.mk' (gmPoint K) (point_mul K)

/-- Actual torus points and coefficient units are isomorphic as groups. -/
def equivalence : Kˣ ≃* (𝟙_ (Over (Spec (.of K))) ⟶ MultiplicativeGroupScheme.gm K) :=
  MulEquiv.ofBijective (pointHom K)
    ⟨point_injective K, PolygonGroupPoints.gmPoint_surjective K⟩

end FLT.Mazur.TorusPointUnitEquiv
