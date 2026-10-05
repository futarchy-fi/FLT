/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicIntegral
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Base change of Weierstrass charts and gluing

The chart squares are cartesian, and their coefficient morphisms glue over the
coefficient base. The cartesian property of the global square is a separate step. -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts

universe u v
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable (S : Type v) [CommRing S] [Algebra R S]

/-- Each Weierstrass chart commutes with arbitrary extension of coefficients. -/
def chartBaseChangeEquiv (b : Bool) :
    S ⊗[R] Ring W b ≃ₐ[S] Ring (W.map (algebraMap R S)) b :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := R) S (MvPolynomial (Fin 2) R) S
    (Ideal.span {equation W b})).trans
    (Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv R S) (by
      simp only [Ideal.map_span, Set.image_singleton]
      change Ideal.span {equation (W.map (algebraMap R S)) b} =
        Ideal.span {MvPolynomial.algebraTensorAlgEquiv R S (1 ⊗ₜ[R] equation W b)}
      rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul, map_equation]))

@[simp] theorem chartBaseChangeEquiv_tmul_mk (b : Bool) (s : S)
    (p : MvPolynomial (Fin 2) R) :
    chartBaseChangeEquiv W S b (s ⊗ₜ[R] Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (s • MvPolynomial.map (algebraMap R S) p) := by
  change Ideal.Quotient.mk _ (MvPolynomial.algebraTensorAlgEquiv R S (s ⊗ₜ[R] p)) = _
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul]

@[simp] theorem chartBaseChangeEquiv_coord (b : Bool) (i : Fin 2) :
    chartBaseChangeEquiv W S b (1 ⊗ₜ[R] coord W b i) =
      coord (W.map (algebraMap R S)) b i := by
  simp [coord]

/-- The coefficient-extension map on either quotient chart ring. -/
def chartCoefficientMap (b : Bool) : Ring W b →+* Ring (W.map (algebraMap R S)) b :=
  (chartBaseChangeEquiv W S b).toRingHom.comp
    Algebra.TensorProduct.includeRight.toRingHom

@[simp] theorem chartCoefficientMap_mk (b : Bool) (p : MvPolynomial (Fin 2) R) :
    chartCoefficientMap W S b (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R S) p) := by
  change chartBaseChangeEquiv W S b (1 ⊗ₜ[R] Ideal.Quotient.mk _ p) = _
  rw [chartBaseChangeEquiv_tmul_mk, one_smul]

@[simp] theorem chartCoefficientMap_coord (b : Bool) (i : Fin 2) :
    chartCoefficientMap W S b (coord W b i) =
      coord (W.map (algebraMap R S)) b i :=
  chartBaseChangeEquiv_coord W S b i

/-- Coefficient extension on the localized overlap. -/
def overlapCoefficientMap (b : Bool) : Overlap W b →+*
    Overlap (W.map (algebraMap R S)) b :=
  IsLocalization.map (Overlap (W.map (algebraMap R S)) b) (chartCoefficientMap W S b)
    (M := Submonoid.powers (coord W b 1))
    (T := Submonoid.powers (coord (W.map (algebraMap R S)) b 1)) (by
      rintro x ⟨n, rfl⟩
      exact ⟨n, by simp⟩)

@[simp] theorem overlapCoefficientMap_algebraMap (b : Bool) (x : Ring W b) :
    overlapCoefficientMap W S b (algebraMap (Ring W b) (Overlap W b) x) =
      algebraMap _ _ (chartCoefficientMap W S b x) :=
  IsLocalization.map_eq _ _

@[simp] theorem overlapCoefficientMap_loc (b : Bool) (i : Fin 2) :
    overlapCoefficientMap W S b (loc W b i) =
      loc (W.map (algebraMap R S)) b i := by
  simp [loc]

@[simp] theorem overlapCoefficientMap_inv (b : Bool) :
    overlapCoefficientMap W S b (inv W b) =
      inv (W.map (algebraMap R S)) b := by
  have h := congrArg (overlapCoefficientMap W S b) (loc_mul_inv W b)
  rw [map_mul, overlapCoefficientMap_loc, map_one] at h
  calc
    overlapCoefficientMap W S b (inv W b) =
        (inv (W.map (algebraMap R S)) b * loc (W.map (algebraMap R S)) b 1) *
          overlapCoefficientMap W S b (inv W b) := by rw [inv_mul_loc, one_mul]
    _ = inv (W.map (algebraMap R S)) b := by rw [mul_assoc, h, mul_one]

@[simp] theorem chartCoefficientMap_scalar (b : Bool) (r : R) :
    chartCoefficientMap W S b (algebraMap R (Ring W b) r) =
      algebraMap S (Ring (W.map (algebraMap R S)) b) (algebraMap R S r) := by
  change chartCoefficientMap W S b (Ideal.Quotient.mk _ (C r)) = _
  rw [chartCoefficientMap_mk, MvPolynomial.map_C]
  rfl

@[simp] theorem overlapCoefficientMap_scalar (b : Bool) (r : R) :
    overlapCoefficientMap W S b (algebraMap R (Overlap W b) r) =
      algebraMap S (Overlap (W.map (algebraMap R S)) b) (algebraMap R S r) := by
  rw [IsScalarTower.algebraMap_apply R (Ring W b),
    overlapCoefficientMap_algebraMap, chartCoefficientMap_scalar,
    ← IsScalarTower.algebraMap_apply S (Ring (W.map (algebraMap R S)) b)]

set_option backward.isDefEq.respectTransparency.types false in
/-- The overlap transition commutes with extension of coefficients. -/
theorem overlapCoefficientMap_transition (b : Bool) :
    (overlapCoefficientMap W S b).comp (transition W b).toRingHom =
      (transition (W.map (algebraMap R S)) b).toRingHom.comp
        (overlapCoefficientMap W S (!b)) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (coord W (!b) 1))
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    change overlapCoefficientMap W S b
      (transition W b (algebraMap R (Overlap W (!b)) r)) =
      transition (W.map (algebraMap R S)) b
        (overlapCoefficientMap W S (!b) (algebraMap R (Overlap W (!b)) r))
    rw [AlgHom.commutes, overlapCoefficientMap_scalar, overlapCoefficientMap_scalar,
      AlgHom.commutes]
  · intro i
    change overlapCoefficientMap W S b (transition W b (loc W (!b) i)) =
      transition (W.map (algebraMap R S)) b
        (overlapCoefficientMap W S (!b) (loc W (!b) i))
    rw [overlapCoefficientMap_loc, transition_loc, transition_loc]
    fin_cases i <;> simp

variable (T : Type u) [CommRing T] [Algebra R T]

/-- The coefficient square of chart rings is a pushout. -/
theorem chartCoefficientMap_isPushout (b : Bool) :
    IsPushout (CommRingCat.ofHom (algebraMap R T))
      (CommRingCat.ofHom (algebraMap R (Ring W b)))
      (CommRingCat.ofHom (algebraMap T (Ring (W.map (algebraMap R T)) b)))
      (CommRingCat.ofHom (chartCoefficientMap W T b)) := by
  refine (CommRingCat.isPushout_tensorProduct R T (Ring W b)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (chartBaseChangeEquiv W T b).toRingEquiv.toCommRingCatIso
    (by simp) (by simp) ?_ ?_
  · ext t
    exact (chartBaseChangeEquiv W T b).commutes t
  · rfl

/-- Coefficient extension gives the actual scheme-theoretic base change of each chart. -/
theorem chartBaseChange_isPullback (b : Bool) :
    IsPullback (Spec.map (CommRingCat.ofHom (chartCoefficientMap W T b)))
      (chartToBase (W.map (algebraMap R T)) b) (chartToBase W b)
      (Spec.map (CommRingCat.ofHom (algebraMap R T))) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ (chartCoefficientMap_isPushout W T b)).flip

/-- The chart morphism induced by extending coefficients. -/
def chartCoefficientMorphism (b : Bool) :
    chart (W.map (algebraMap R T)) b ⟶ chart W b :=
  Spec.map (CommRingCat.ofHom (chartCoefficientMap W T b))

/-- The corresponding morphism on the common open subset. -/
def overlapCoefficientMorphism (b : Bool) :
    Spec (.of (Overlap (W.map (algebraMap R T)) b)) ⟶ Spec (.of (Overlap W b)) :=
  Spec.map (CommRingCat.ofHom (overlapCoefficientMap W T b))

@[reassoc] theorem overlapInclusion_coefficient (b : Bool) :
    overlapInclusion (W.map (algebraMap R T)) b ≫ chartCoefficientMorphism W T b =
      overlapCoefficientMorphism W T b ≫ overlapInclusion W b := by
  unfold overlapInclusion chartCoefficientMorphism overlapCoefficientMorphism
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun x ↦ (overlapCoefficientMap_algebraMap W T b x).symm)

@[reassoc] theorem overlapIso_coefficient :
    (overlapIso (W.map (algebraMap R T))).hom ≫ overlapCoefficientMorphism W T true =
      overlapCoefficientMorphism W T false ≫ (overlapIso W).hom := by
  rw [overlapIso_hom, overlapIso_hom]
  unfold overlapCoefficientMorphism
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f))
    (overlapCoefficientMap_transition W T false).symm

@[reassoc] theorem overlapRight_coefficient :
    overlapRight (W.map (algebraMap R T)) ≫ chartCoefficientMorphism W T true =
      overlapCoefficientMorphism W T false ≫ overlapRight W := by
  simp only [overlapRight, Category.assoc, overlapInclusion_coefficient]
  rw [← Category.assoc, overlapIso_coefficient, Category.assoc]

theorem coefficient_gluing :
    overlapInclusion (W.map (algebraMap R T)) false ≫
        (chartCoefficientMorphism W T false ≫ affineChart W) =
      overlapRight (W.map (algebraMap R T)) ≫
        (chartCoefficientMorphism W T true ≫ infinityChart W) := by
  rw [overlapInclusion_coefficient_assoc, overlapRight_coefficient_assoc]
  exact congrArg (fun f ↦ overlapCoefficientMorphism W T false ≫ f) (overlap_condition W)

/-- The global morphism obtained by gluing the coefficient-extension maps. -/
def coefficientMorphism : scheme (W.map (algebraMap R T)) ⟶ scheme W :=
  CategoryTheory.Limits.pushout.desc
    (chartCoefficientMorphism W T false ≫ affineChart W)
    (chartCoefficientMorphism W T true ≫ infinityChart W) (coefficient_gluing W T)

@[reassoc (attr := simp)] theorem affineChart_coefficientMorphism :
    affineChart (W.map (algebraMap R T)) ≫ coefficientMorphism W T =
      chartCoefficientMorphism W T false ≫ affineChart W :=
  CategoryTheory.Limits.pushout.inl_desc _ _ _

@[reassoc (attr := simp)] theorem infinityChart_coefficientMorphism :
    infinityChart (W.map (algebraMap R T)) ≫ coefficientMorphism W T =
      chartCoefficientMorphism W T true ≫ infinityChart W :=
  CategoryTheory.Limits.pushout.inr_desc _ _ _

@[reassoc] theorem chartCoefficientMorphism_toBase (b : Bool) :
    chartCoefficientMorphism W T b ≫ chartToBase W b =
      chartToBase (W.map (algebraMap R T)) b ≫
        Spec.map (CommRingCat.ofHom (algebraMap R T)) :=
  (chartBaseChange_isPullback W T b).w

/-- The glued coefficient morphism lies over the specified morphism of bases. -/
@[reassoc] theorem coefficientMorphism_toBase :
    coefficientMorphism W T ≫ toBase W =
      toBase (W.map (algebraMap R T)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
  apply CategoryTheory.Limits.pushout.hom_ext
  · change affineChart (W.map (algebraMap R T)) ≫ _ =
      affineChart (W.map (algebraMap R T)) ≫ _
    simp only [affineChart_coefficientMorphism_assoc,
      affineChart_toBase, affineChart_toBase_assoc, chartCoefficientMorphism_toBase]
  · change infinityChart (W.map (algebraMap R T)) ≫ _ =
      infinityChart (W.map (algebraMap R T)) ≫ _
    simp only [infinityChart_coefficientMorphism_assoc,
      infinityChart_toBase, infinityChart_toBase_assoc, chartCoefficientMorphism_toBase]

end WeierstrassCurve.CubicCharts
