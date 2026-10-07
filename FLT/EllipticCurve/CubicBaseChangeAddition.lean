/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicBaseChangeGlobal
public import FLT.EllipticCurve.CubicVariableChangeGroup

/-! # Addition and zero under coefficient extension

Coefficient extension preserves the distinguished point at infinity and
the evaluation of affine points. Comparison with classical field points
then proves compatibility with addition on reduced schemes of points,
and with the actual global addition over a noetherian reduced new base.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable (S : Type u) [CommRing S] [Algebra R S]

/-- Origin evaluation on the infinity chart commutes with coefficient extension. -/
theorem infinityOrigin_coefficient :
    (infinityOrigin (W.map (algebraMap R S))).toRingHom.comp (chartCoefficientMap W S true) =
      (algebraMap R S).comp (infinityOrigin W).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext'
  · ext r
    change infinityOrigin (W.map (algebraMap R S))
        (chartCoefficientMap W S true (Ideal.Quotient.mk _ (MvPolynomial.C r))) = _
    rw [chartCoefficientMap_mk, MvPolynomial.map_C]
    change infinityOrigin (W.map (algebraMap R S))
        (algebraMap S (Ring (W.map (algebraMap R S)) true) (algebraMap R S r)) =
      algebraMap R S (infinityOrigin W (algebraMap R (Ring W true) r))
    rw [AlgHom.commutes, AlgHom.commutes]
    simp
  · intro i
    change infinityOrigin (W.map (algebraMap R S))
        (chartCoefficientMap W S true (coord W true i)) =
      algebraMap R S (infinityOrigin W (coord W true i))
    rw [chartCoefficientMap_coord, infinityOrigin_coord, infinityOrigin_coord, map_zero]

/-- The coefficient morphism preserves the section at infinity. -/
theorem infinity_coefficientMorphism :
    infinity (W.map (algebraMap R S)) ≫ coefficientMorphism W S =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ infinity W := by
  have h : InfinityChart.infinity (W.map (algebraMap R S)) ≫ chartCoefficientMorphism W S true =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ InfinityChart.infinity W := by
    change Spec.map (CommRingCat.ofHom (infinityOrigin _).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (chartCoefficientMap W S true)) =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫
        Spec.map (CommRingCat.ofHom (infinityOrigin W).toRingHom)
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f : Ring W true →+* S => Spec.map (CommRingCat.ofHom f))
      (infinityOrigin_coefficient W S)
  unfold infinity
  rw [Category.assoc, infinityChart_coefficientMorphism, ← Category.assoc, h, Category.assoc]

section Evaluation
variable {K : Type u} [CommRing K] [Algebra S K] [Algebra R K] [IsScalarTower R S K]

/-- Affine evaluation commutes with coefficient extension in an algebra tower. -/
theorem affineEvaluation_coefficient (x y : K)
    (h : ((W.map (algebraMap R S)).map (algebraMap S K)).toAffine.Equation x y)
    (h' : (W.map (algebraMap R K)).toAffine.Equation x y) :
    (affineEvaluation (W.map (algebraMap R S)) x y h).toRingHom.comp
        (chartCoefficientMap W S false) =
      (affineEvaluation W x y h').toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext'
  · ext r
    change affineEvaluation (W.map (algebraMap R S)) x y h
        (chartCoefficientMap W S false (Ideal.Quotient.mk _ (MvPolynomial.C r))) = _
    rw [chartCoefficientMap_mk, MvPolynomial.map_C]
    change affineEvaluation (W.map (algebraMap R S)) x y h
        (algebraMap S (Ring (W.map (algebraMap R S)) false) (algebraMap R S r)) =
      affineEvaluation W x y h' (algebraMap R (Ring W false) r)
    rw [AlgHom.commutes, AlgHom.commutes]
    exact (IsScalarTower.algebraMap_apply R S K r).symm
  · intro i
    change affineEvaluation (W.map (algebraMap R S)) x y h
        (chartCoefficientMap W S false (coord W false i)) =
      affineEvaluation W x y h' (coord W false i)
    rw [chartCoefficientMap_coord, affineEvaluation_coord, affineEvaluation_coord]

/-- Affine point morphisms commute with coefficient extension. -/
theorem affineFieldPoint_coefficient (x y : K)
    (h : ((W.map (algebraMap R S)).map (algebraMap S K)).toAffine.Equation x y)
    (h' : (W.map (algebraMap R K)).toAffine.Equation x y) :
    (Spec.map (CommRingCat.ofHom
        (affineEvaluation (W.map (algebraMap R S)) x y h).toRingHom) ≫
        affineChart (W.map (algebraMap R S))) ≫ coefficientMorphism W S =
      Spec.map (CommRingCat.ofHom (affineEvaluation W x y h').toRingHom) ≫ affineChart W := by
  rw [Category.assoc, affineChart_coefficientMorphism, ← Category.assoc]
  apply congrArg (fun f => f ≫ affineChart W)
  change Spec.map (CommRingCat.ofHom
      (affineEvaluation (W.map (algebraMap R S)) x y h).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (chartCoefficientMap W S false)) = _
  rw [← Spec.map_comp]
  exact congrArg (fun f : Ring W false →+* K => Spec.map (CommRingCat.ofHom f))
    (affineEvaluation_coefficient W S x y h h')

end Evaluation

section Fields
variable {K : Type u} [Field K] [Algebra S K] [Algebra R K] [IsScalarTower R S K]

/-- The classical point groups agree after composing coefficient extensions. -/
def coefficientPointEquiv [DecidableEq K] :
    ((W.map (algebraMap R S)).map (algebraMap S K)).toAffine.Point ≃+
      (W.map (algebraMap R K)).toAffine.Point :=
  Affine.Point.equivOfEq (by
    rw [WeierstrassCurve.map_map, ← IsScalarTower.algebraMap_eq R S K])

/-- The morphisms of affine coefficient spectra compose along the algebra tower. -/
theorem coefficient_base_comp :
    Spec.map (CommRingCat.ofHom (algebraMap S K)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R S)) =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
  rw [← Spec.map_comp]
  exact congrArg (fun f : R →+* K => Spec.map (CommRingCat.ofHom f))
    (IsScalarTower.algebraMap_eq R S K).symm

/-- Coefficient extension transports classical point morphisms. -/
theorem fieldPointMorphism_coefficient [DecidableEq K]
    (P : ((W.map (algebraMap R S)).map (algebraMap S K)).toAffine.Point) :
    fieldPointMorphism (W.map (algebraMap R S)) P ≫ coefficientMorphism W S =
      fieldPointMorphism W (coefficientPointEquiv W S P) := by
  cases P with
  | zero =>
    simp only [← Affine.Point.zero_def, map_zero, fieldPointMorphism,
      Category.assoc, infinity_coefficientMorphism]
    rw [← Category.assoc, coefficient_base_comp S]
  | some x y h =>
    unfold coefficientPointEquiv
    erw [Affine.Point.equivOfEq_some]
    simp only [fieldPointMorphism]
    exact affineFieldPoint_coefficient W S x y _ _

/-- Coefficient extension preserves addition on field-valued points. -/
theorem addMorphisms_coefficient_field [W.IsElliptic]
    (f g : Spec (.of K) ⟶ scheme (W.map (algebraMap R S)))
    (hf : f ≫ toBase (W.map (algebraMap R S)) =
      Spec.map (CommRingCat.ofHom (algebraMap S K)))
    (hfg : f ≫ toBase (W.map (algebraMap R S)) =
      g ≫ toBase (W.map (algebraMap R S))) :
    addMorphisms (W.map (algebraMap R S)) f g hfg ≫ coefficientMorphism W S =
      addMorphisms W (f ≫ coefficientMorphism W S) (g ≫ coefficientMorphism W S)
        (by
          simpa only [Category.assoc, coefficientMorphism_toBase] using
            congrArg (fun h => h ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))) hfg) := by
  classical
  obtain ⟨P, rfl⟩ := fieldPointMorphism_surjective (W.map (algebraMap R S)) f hf
  obtain ⟨Q, rfl⟩ := fieldPointMorphism_surjective (W.map (algebraMap R S)) g
    (hfg.symm.trans hf)
  simp only [addMorphisms_fieldPoints, fieldPointMorphism_coefficient, map_add]
end Fields

/-- Coefficient extension preserves addition on reduced schemes of points. -/
theorem addMorphisms_coefficient_of_isReduced [W.IsElliptic]
    {X : Scheme.{u}} [AlgebraicGeometry.IsReduced X]
    (f g : X ⟶ scheme (W.map (algebraMap R S)))
    (hfg : f ≫ toBase (W.map (algebraMap R S)) =
      g ≫ toBase (W.map (algebraMap R S))) :
    addMorphisms (W.map (algebraMap R S)) f g hfg ≫ coefficientMorphism W S =
      addMorphisms W (f ≫ coefficientMorphism W S) (g ≫ coefficientMorphism W S)
        (by
          simpa only [Category.assoc, coefficientMorphism_toBase] using
            congrArg (fun h => h ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))) hfg) := by
  apply ext_of_fromSpecResidueField_eq _ _ (toBase W) Set.univ dense_univ
  · intro x _
    obtain ⟨φ, hφ⟩ := Spec.map_surjective
      (X.fromSpecResidueField x ≫ f ≫ toBase (W.map (algebraMap R S)))
    let K : Type u := IsLocalRing.ResidueField (X.presheaf.stalk x)
    let : Algebra S K := φ.hom.toAlgebra
    let : Algebra R K := ((algebraMap S K).comp (algebraMap R S)).toAlgebra
    have : IsScalarTower R S K := IsScalarTower.of_algebraMap_eq' rfl
    have hf : (X.fromSpecResidueField x ≫ f) ≫ toBase (W.map (algebraMap R S)) =
        Spec.map (CommRingCat.ofHom (algebraMap S K)) := by
      change (X.fromSpecResidueField x ≫ f) ≫ toBase (W.map (algebraMap R S)) = Spec.map φ
      simpa only [Category.assoc] using hφ.symm
    rw [← Category.assoc, addMorphisms_precomp, addMorphisms_precomp]
    simpa only [Category.assoc] using
      addMorphisms_coefficient_field W S (K := K)
        (X.fromSpecResidueField x ≫ f) (X.fromSpecResidueField x ≫ g) hf
        (by simp only [Category.assoc, hfg])
  · simp only [Category.assoc, coefficientMorphism_toBase, addMorphisms_toBase]
    rw [← Category.assoc, addMorphisms_toBase, Category.assoc]

/-- The actual global addition commutes with coefficient extension. -/
theorem addition_coefficient [IsNoetherianRing S] [_root_.IsReduced S] [W.IsElliptic] :
    addition (W.map (algebraMap R S)) ≫ coefficientMorphism W S =
      addMorphisms W
        (pullback.fst (toBase (W.map (algebraMap R S)))
          (toBase (W.map (algebraMap R S))) ≫ coefficientMorphism W S)
        (pullback.snd (toBase (W.map (algebraMap R S)))
          (toBase (W.map (algebraMap R S))) ≫ coefficientMorphism W S)
        (by
          simpa only [Category.assoc, coefficientMorphism_toBase] using
            congrArg (fun h => h ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
              (pullback.condition (f := toBase (W.map (algebraMap R S)))
                (g := toBase (W.map (algebraMap R S))))) := by
  have : IsLocallyNoetherian (scheme (W.map (algebraMap R S))) :=
    LocallyOfFiniteType.isLocallyNoetherian (toBase (W.map (algebraMap R S)))
  have : AlgebraicGeometry.IsReduced
      (pullback (toBase (W.map (algebraMap R S))) (toBase (W.map (algebraMap R S)))) :=
    inferInstance
  have h := addMorphisms_coefficient_of_isReduced W S
    (pullback.fst (toBase (W.map (algebraMap R S))) (toBase (W.map (algebraMap R S))))
    (pullback.snd (toBase (W.map (algebraMap R S))) (toBase (W.map (algebraMap R S))))
    pullback.condition
  simpa only [addMorphisms, pullback.lift_fst_snd, Category.id_comp] using h

end WeierstrassCurve.CubicCharts
