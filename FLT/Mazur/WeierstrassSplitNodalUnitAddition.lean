/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalSmoothGroupComparison
public import FLT.Mazur.LaurentUnitMultiplication

/-!
# Original smooth addition on arbitrary algebra-valued Laurent parameters

This is the independently constructed smooth addition, evaluated on two
units of any coefficient algebra. The equality is an equality of scheme
morphisms and therefore also retains nonreduced source schemes.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (a : Rˣ) (p q : Aˣ)
local notation "s" => Spec.map (CommRingCat.ofHom (algebraMap R A))
local notation "G" => MultiplicativeGroupScheme.gm R
local notation "I" => splitNodalRelativeSmoothOverIso a

/-- Unit evaluation as an actual coefficient-preserving morphism to the torus. -/
def laurentUnitOverPoint (p : Aˣ) : Over.mk s ⟶ G :=
  Over.homMk (Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R) p).toRingHom))
    (specAlgHom_structure (LaurentUnitPoints.evalUnit p))

/-- The two unit evaluations multiply on the full affine source scheme. -/
theorem laurentUnitOverPoint_mul :
    lift (laurentUnitOverPoint (R := R) p) (laurentUnitOverPoint q) ≫ μ[G] =
      laurentUnitOverPoint (p * q) := by
  apply Over.OverMorphism.ext
  let hpair := (laurentUnitOverPoint (R := R) p).w.trans
    (laurentUnitOverPoint (R := R) q).w.symm
  change pullback.lift (Spec.map _) (Spec.map _) hpair ≫ μ[G].left = Spec.map _
  rw [MultiplicativeGroupScheme.multiplication_left, ← Category.assoc]
  have ht : pullback.lift
      (Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R) p).toRingHom))
      (Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R) q).toRingHom))
      hpair ≫ (pullbackSpecIso R R[T;T⁻¹] R[T;T⁻¹]).hom =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap
          (LaurentUnitPoints.evalUnit (R := R) p)
          (LaurentUnitPoints.evalUnit (R := R) q)).toRingHom) := by
    apply (cancel_mono (pullbackSpecIso R R[T;T⁻¹] R[T;T⁻¹]).inv).mp
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc]
      erw [pullbackSpecIso_inv_fst]
      rw [← Spec.map_comp]
      congr 1
      exact congrArg (fun h => CommRingCat.ofHom (AlgHom.toRingHom h))
        (Algebra.TensorProduct.productMap_left
          (LaurentUnitPoints.evalUnit (R := R) p) (LaurentUnitPoints.evalUnit q)).symm
    · rw [pullback.lift_snd, Category.assoc]
      erw [pullbackSpecIso_inv_snd]
      rw [← Spec.map_comp]
      congr 1
      exact congrArg (fun h => CommRingCat.ofHom (AlgHom.toRingHom h))
        (Algebra.TensorProduct.productMap_right
          (LaurentUnitPoints.evalUnit (R := R) p) (LaurentUnitPoints.evalUnit q)).symm
  rw [ht, ← Spec.map_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom h)))
    (laurentUnit_product_comul (R := R) p q)

/-- The original smooth parameter determined by a unit of the source algebra. -/
def splitNodalSmoothUnitInput (p : Aˣ) : Over.mk s ⟶ splitNodalSmoothOver a :=
  laurentUnitOverPoint p ≫ (I).hom

/-- The independently constructed smooth law multiplies the actual Laurent parameters. -/
theorem splitNodalSmoothUnitInput_addition :
    (lift (splitNodalSmoothUnitInput a p) (splitNodalSmoothUnitInput a q)).left ≫
        smoothFactorAddition (splitNodalEquation a) =
      (splitNodalSmoothUnitInput a (p * q)).left := by
  let _ := splitNodalSmoothCommGrpObj a
  have hh : lift (splitNodalSmoothUnitInput a p) (splitNodalSmoothUnitInput a q) ≫
      μ[splitNodalSmoothOver a] = splitNodalSmoothUnitInput a (p * q) := by
    rw [splitNodalSmoothUnitInput, splitNodalSmoothUnitInput, ← lift_map_assoc,
      ← IsMonHom.mul_hom, ← Category.assoc, laurentUnitOverPoint_mul]
    rfl
  rw [splitNodalSmoothGroup_mul_eq] at hh
  exact congrArg (fun h => h.left) hh

end FLT.Mazur.WeierstrassIntegralChart
