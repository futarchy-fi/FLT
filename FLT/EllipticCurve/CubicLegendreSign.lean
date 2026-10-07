/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicLegendreSymmetries

/-! # The sign ambiguity of local Legendre maps

Changing the square root used for a Legendre symmetry changes the actual
curve morphism by elliptic negation. The proof compares affine coordinate
pullbacks and uses the schematic density of the affine chart to identify
the global maps. It holds over arbitrary commutative coefficient rings.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R]

/-- Coordinate pullback after identifying the transformed equation. -/
def variableChangeIdentifiedAffineMap (W V : WeierstrassCurve R) (C : VariableChange R)
    (h : C • W = V) : Ring W false →ₐ[R] Ring V false :=
  (chartRingCongr h false).toAlgHom.comp (variableChangeAffineMap W C)

/-- The identified pullback retains the explicit coordinate formulas. -/
theorem variableChangeIdentifiedAffineMap_coord (W V : WeierstrassCurve R)
    (C : VariableChange R) (h : C • W = V) (i : Fin 2) :
    variableChangeIdentifiedAffineMap W V C h (coord W false i) =
      ![(algebraMap R _ (C.u : R)) ^ 2 * coord V false 0 + algebraMap R _ C.r,
        (algebraMap R _ (C.u : R)) ^ 3 * coord V false 1 +
          (algebraMap R _ (C.u : R)) ^ 2 * algebraMap R _ C.s * coord V false 0 +
            algebraMap R _ C.t] i := by
  fin_cases i <;> simp [variableChangeIdentifiedAffineMap, variableChangeAffineCoords]

/-- The identified curve map has the stated affine coordinate pullback. -/
theorem affineChart_variableChangeCongr (W V : WeierstrassCurve R)
    (C : VariableChange R) (h : C • W = V) :
    affineChart V ≫ (variableChangeCongrOverIso W V C h).hom.left =
      Spec.map (CommRingCat.ofHom (variableChangeIdentifiedAffineMap W V C h).toRingHom) ≫
        affineChart W := by
  subst V
  change affineChart (C • W) ≫ variableChangeMorphism W C =
    variableChangeAffineMorphism W C ≫ affineChart W
  exact affineChart_variableChange W C

/-- A scaling and translation without the linear y-correction terms. -/
def signCoordinateChange (u : Rˣ) (r : R) : VariableChange R := ⟨u, r, 0, 0⟩

/-- Changing the scaling sign for an equation without mixed y-terms composes with negation. -/
theorem signCoordinateChange_affine (W V : WeierstrassCurve R)
    (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (u : Rˣ) (r : R)
    (h : signCoordinateChange u r • W = V)
    (hneg : signCoordinateChange (-u) r • W = V) :
    variableChangeIdentifiedAffineMap W V (signCoordinateChange (-u) r) hneg =
      (variableChangeIdentifiedAffineMap W V (signCoordinateChange u r) h).comp
        (affineNegationEquiv W).toAlgHom := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change variableChangeIdentifiedAffineMap W V (signCoordinateChange (-u) r) hneg
      (coord W false i) =
    variableChangeIdentifiedAffineMap W V (signCoordinateChange u r) h
      (affineNegationEquiv W (coord W false i))
  fin_cases i
  · simp [variableChangeIdentifiedAffineMap_coord, signCoordinateChange]
  · simp [variableChangeIdentifiedAffineMap_coord, signCoordinateChange, ha₁, ha₃]
    ring

/-- The affine sign identity identifies the actual global curve morphisms. -/
theorem signCoordinateChange_morphism (W V : WeierstrassCurve R)
    (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (u : Rˣ) (r : R)
    (h : signCoordinateChange u r • W = V)
    (hneg : signCoordinateChange (-u) r • W = V) :
    (variableChangeCongrOverIso W V (signCoordinateChange (-u) r) hneg).hom.left =
      (variableChangeCongrOverIso W V (signCoordinateChange u r) h).hom.left ≫ negation W := by
  apply affineChart_hom_ext V (toBase W)
  · rw [Category.assoc, negation_toBase]
    exact (variableChangeCongrOverIso W V (signCoordinateChange (-u) r) hneg).hom.w.trans
      (variableChangeCongrOverIso W V (signCoordinateChange u r) h).hom.w.symm
  · rw [affineChart_variableChangeCongr, ← Category.assoc, affineChart_variableChangeCongr,
      Category.assoc, affineChart_negation, ← Category.assoc]
    rw [signCoordinateChange_affine W V ha₁ ha₃ u r h hneg]
    change Spec.map (CommRingCat.ofHom
        (((variableChangeIdentifiedAffineMap W V (signCoordinateChange u r) h).comp
          (affineNegationEquiv W).toAlgHom).toRingHom)) ≫ affineChart W = _
    rw [affineNegation, ← Spec.map_comp]
    rfl

/-- The sign identity as an equality of morphisms over the coefficient base. -/
theorem signCoordinateChange_over (W V : WeierstrassCurve R)
    (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (u : Rˣ) (r : R)
    (h : signCoordinateChange u r • W = V)
    (hneg : signCoordinateChange (-u) r • W = V) :
    (variableChangeCongrOverIso W V (signCoordinateChange (-u) r) hneg).hom =
      (variableChangeCongrOverIso W V (signCoordinateChange u r) h).hom ≫ negationOver W := by
  apply Over.OverMorphism.ext
  exact signCoordinateChange_morphism W V ha₁ ha₃ u r h hneg

attribute [local irreducible] variableChangeCongrOverIso

/-- The two square-root choices for the swap differ by elliptic negation. -/
theorem legendreSwapOverIso_neg (l : R) (u : Rˣ) (hu : (u : R) ^ 2 = -1) :
    (legendreSwapOverIso l (-u) (by simpa only [Units.val_neg, neg_sq] using hu)).hom =
      (legendreSwapOverIso l u hu).hom ≫ negationOver (legendreCurve l) := by
  simpa only [legendreSwapOverIso, legendreSwapChange, signCoordinateChange,
    Over.comp_left, negationOver, Over.homMk_left] using
    signCoordinateChange_over (legendreCurve l) (legendreCurve (1 - l))
    rfl rfl u 1 (legendreSwapChange_curve l u hu)
      (legendreSwapChange_curve l (-u) (by simpa only [Units.val_neg, neg_sq] using hu))

/-- The two square-root choices for the reciprocal differ by elliptic negation. -/
theorem legendreReciprocalOverIso_neg (l u : Rˣ) (hu : (u : R) ^ 2 = l) :
    (legendreReciprocalOverIso l (-u) (by simpa only [Units.val_neg, neg_sq] using hu)).hom =
      (legendreReciprocalOverIso l u hu).hom ≫ negationOver (legendreCurve (l : R)) := by
  simpa only [legendreReciprocalOverIso, legendreReciprocalChange, signCoordinateChange,
    Over.comp_left, negationOver, Over.homMk_left] using
    signCoordinateChange_over (legendreCurve (l : R))
    (legendreCurve ((l⁻¹ : Rˣ) : R)) rfl rfl u 0 (legendreReciprocalChange_curve l u hu)
      (legendreReciprocalChange_curve l (-u) (by simpa only [Units.val_neg, neg_sq] using hu))

end WeierstrassCurve.CubicCharts
