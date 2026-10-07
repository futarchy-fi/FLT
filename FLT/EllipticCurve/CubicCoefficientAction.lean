/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicVariableChangeBaseChange
public import FLT.EllipticCurve.CubicCyclicQuadraticDescent
/-! # Coefficient actions on the glued cubic

An endomorphism of the coefficient algebra acts on both cubic charts through
their tensor-product presentations. The chart maps agree with the unique
global map specified by the coefficient pullback square.

This action conjugates an admissible coordinate change to the change obtained
by acting on its coefficients. For a quadratic root algebra the resulting
global action is the pulled-back root-sign involution used in descent.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable (S : Type u) [CommRing S] [Algebra R S] (σ : S →ₐ[R] S)

/-- The coefficient action on a chart via its tensor-product presentation. -/
def chartCoefficientEnd (b : Bool) :
    Ring (W.map (algebraMap R S)) b →+* Ring (W.map (algebraMap R S)) b :=
  (chartBaseChangeEquiv W S b).toRingHom.comp
    ((Algebra.TensorProduct.map σ (AlgHom.id R (Ring W b))).toRingHom.comp
      (chartBaseChangeEquiv W S b).symm.toRingHom)

/-- The chart action applies the coefficient endomorphism to the first tensor factor. -/
theorem chartCoefficientEnd_tmul (b : Bool) (s : S) (x : Ring W b) :
    chartCoefficientEnd W S σ b (chartBaseChangeEquiv W S b (s ⊗ₜ[R] x)) =
      chartBaseChangeEquiv W S b (σ s ⊗ₜ[R] x) := by
  simp [chartCoefficientEnd]

/-- The coefficient action fixes the chart coordinates. -/
theorem chartCoefficientEnd_coord (b : Bool) (i : Fin 2) :
    chartCoefficientEnd W S σ b (coord (W.map (algebraMap R S)) b i) =
      coord (W.map (algebraMap R S)) b i := by
  rw [← chartBaseChangeEquiv_coord, chartCoefficientEnd_tmul, map_one,
    chartBaseChangeEquiv_coord]

/-- The chart action restricts to the specified action on scalars. -/
theorem chartCoefficientEnd_scalar (b : Bool) (s : S) :
    chartCoefficientEnd W S σ b (algebraMap S (Ring (W.map (algebraMap R S)) b) s) =
      algebraMap S (Ring (W.map (algebraMap R S)) b) (σ s) := by
  have ht (t : S) : chartBaseChangeEquiv W S b (t ⊗ₜ[R] (1 : Ring W b)) =
      algebraMap S (Ring (W.map (algebraMap R S)) b) t := (chartBaseChangeEquiv W S b).commutes t
  rw [← ht, chartCoefficientEnd_tmul, ht]

/-- The chart action fixes the original coefficient-extension map. -/
theorem chartCoefficientEnd_coefficient (b : Bool) :
    (chartCoefficientEnd W S σ b).comp (chartCoefficientMap W S b) =
      chartCoefficientMap W S b := by
  apply RingHom.ext
  intro x
  change chartCoefficientEnd W S σ b (chartBaseChangeEquiv W S b (1 ⊗ₜ[R] x)) = _
  rw [chartCoefficientEnd_tmul, map_one]
  rfl

/-- The coefficient action fixes the original base scheme. -/
theorem coefficientEnd_base :
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S)) =
        Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact σ.commutes x

/-- The global coefficient action defined by the cartesian coefficient square. -/
def coefficientEndMorphism :
    scheme (W.map (algebraMap R S)) ⟶ scheme (W.map (algebraMap R S)) :=
  (coefficientMorphism_isPullback W S).lift (coefficientMorphism W S)
    (toBase (W.map (algebraMap R S)) ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)) (by
      rw [Category.assoc, coefficientEnd_base, coefficientMorphism_toBase])

/-- The global coefficient action fixes the original cubic projection. -/
@[reassoc (attr := simp)]
theorem coefficientEndMorphism_coefficient :
    coefficientEndMorphism W S σ ≫ coefficientMorphism W S = coefficientMorphism W S :=
  (coefficientMorphism_isPullback W S).lift_fst _ _ _

/-- The global coefficient action induces the specified map of coefficient bases. -/
@[reassoc (attr := simp)]
theorem coefficientEndMorphism_toBase :
    coefficientEndMorphism W S σ ≫ toBase (W.map (algebraMap R S)) =
      toBase (W.map (algebraMap R S)) ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) :=
  (coefficientMorphism_isPullback W S).lift_snd _ _ _

/-- The chart action lies over the coefficient-base action. -/
theorem chartCoefficientEnd_toBase (b : Bool) :
    Spec.map (CommRingCat.ofHom (chartCoefficientEnd W S σ b)) ≫
      chartToBase (W.map (algebraMap R S)) b =
        chartToBase (W.map (algebraMap R S)) b ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) := by
  dsimp only [chartToBase]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  exact chartCoefficientEnd_scalar W S σ b x

/-- The explicit chart action agrees with the global coefficient action. -/
theorem sourceChart_coefficientEnd (b : Bool) :
    sourceChart (W.map (algebraMap R S)) b ≫ coefficientEndMorphism W S σ =
      Spec.map (CommRingCat.ofHom (chartCoefficientEnd W S σ b)) ≫
        sourceChart (W.map (algebraMap R S)) b := by
  apply (coefficientMorphism_isPullback W S).hom_ext
  · simp only [Category.assoc, coefficientEndMorphism_coefficient,
      sourceChart_coefficientMorphism]
    rw [← Category.assoc]
    change _ = (Spec.map (CommRingCat.ofHom (chartCoefficientEnd W S σ b)) ≫
      Spec.map (CommRingCat.ofHom (chartCoefficientMap W S b))) ≫ sourceChart W b
    rw [← Spec.map_comp]
    change _ = Spec.map (CommRingCat.ofHom
      ((chartCoefficientEnd W S σ b).comp (chartCoefficientMap W S b))) ≫ sourceChart W b
    rw [chartCoefficientEnd_coefficient]
    rfl
  · rw [Category.assoc, coefficientEndMorphism_toBase, ← Category.assoc,
      sourceChart_toBase, Category.assoc, sourceChart_toBase]
    exact (chartCoefficientEnd_toBase W S σ b).symm


/-- The extended curve equation is fixed over its field or ring of definition. -/
theorem coefficientEnd_curve_fixed :
    (W.map (algebraMap R S)).map σ.toRingHom = W.map (algebraMap R S) := by
  rw [WeierstrassCurve.map_map]
  congr 1
  ext x
  exact σ.commutes x

variable (V : WeierstrassCurve R) (C : VariableChange S)
variable (h : C • W.map (algebraMap R S) = V.map (algebraMap R S))

include h in
/-- Acting on a coordinate change preserves its identified target equation. -/
theorem coefficientEnd_variableChange_equation :
    C.map σ.toRingHom • W.map (algebraMap R S) = V.map (algebraMap R S) := by
  conv_lhs => rw [← coefficientEnd_curve_fixed W S σ]
  rw [map_variableChange, h, coefficientEnd_curve_fixed]

/-- Coefficient action conjugates the explicit affine coordinate pullbacks. -/
theorem coefficientEnd_variableChange_affine :
    (chartCoefficientEnd V S σ false).comp
      (variableChangeIdentifiedAffineMap (W.map (algebraMap R S)) (V.map (algebraMap R S))
        C h).toRingHom =
      (variableChangeIdentifiedAffineMap (W.map (algebraMap R S)) (V.map (algebraMap R S))
        (C.map σ.toRingHom) (coefficientEnd_variableChange_equation W S σ V C h)).toRingHom.comp
          (chartCoefficientEnd W S σ false) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro s
    change chartCoefficientEnd V S σ false
      (variableChangeIdentifiedAffineMap (W.map (algebraMap R S)) (V.map (algebraMap R S))
        C h (algebraMap S _ s)) =
      variableChangeIdentifiedAffineMap (W.map (algebraMap R S)) (V.map (algebraMap R S))
        (C.map σ.toRingHom) (coefficientEnd_variableChange_equation W S σ V C h)
          (chartCoefficientEnd W S σ false (algebraMap S _ s))
    rw [AlgHom.commutes, chartCoefficientEnd_scalar, chartCoefficientEnd_scalar, AlgHom.commutes]
  · intro i
    change chartCoefficientEnd V S σ false
      (variableChangeIdentifiedAffineMap (W.map (algebraMap R S)) (V.map (algebraMap R S))
        C h (coord _ false i)) =
      variableChangeIdentifiedAffineMap (W.map (algebraMap R S)) (V.map (algebraMap R S))
        (C.map σ.toRingHom) (coefficientEnd_variableChange_equation W S σ V C h)
          (chartCoefficientEnd W S σ false (coord _ false i))
    rw [variableChangeIdentifiedAffineMap_coord, chartCoefficientEnd_coord,
      variableChangeIdentifiedAffineMap_coord]
    fin_cases i <;> simp [VariableChange.map, map_add, map_mul, map_pow,
      chartCoefficientEnd_scalar, chartCoefficientEnd_coord]

/-- The global coefficient action restricts to the stated affine pullback. -/
theorem affineChart_coefficientEnd :
    affineChart (W.map (algebraMap R S)) ≫ coefficientEndMorphism W S σ =
      Spec.map (CommRingCat.ofHom (chartCoefficientEnd W S σ false)) ≫
        affineChart (W.map (algebraMap R S)) :=
  sourceChart_coefficientEnd W S σ false

attribute [local irreducible] variableChangeCongrOverIso coefficientEndMorphism

private theorem specMap_ringHom_comp {A B D : Type u}
    [CommRing A] [CommRing B] [CommRing D] (f : B →+* D) (g : A →+* B) :
    Spec.map (CommRingCat.ofHom (f.comp g)) =
      Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom g) :=
  Spec.map_comp _ _

private theorem specMap_ringHom_square {A B C D : Type u}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : B →+* D) (f' : A →+* C) (g' : C →+* D)
    (h : g.comp f = g'.comp f') :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom g') ≫ Spec.map (CommRingCat.ofHom f') := by
  rw [← specMap_ringHom_comp, ← specMap_ringHom_comp, h]

private theorem square_comp {A B C D E F : Scheme.{u}}
    {i : A ⟶ B} {j : C ⟶ D} {k : E ⟶ F}
    {f : B ⟶ D} {g : D ⟶ F} {f' : A ⟶ C} {g' : C ⟶ E}
    (h₁ : i ≫ f = f' ≫ j) (h₂ : j ≫ g = g' ≫ k) :
    i ≫ (f ≫ g) = (f' ≫ g') ≫ k := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

/-- The conjugacy identity holds after restriction to the affine chart. -/
theorem coefficientEnd_variableChange_chart :
    affineChart (V.map (algebraMap R S)) ≫ (coefficientEndMorphism V S σ ≫
      (variableChangeCongrOverIso (W.map (algebraMap R S)) (V.map (algebraMap R S)) C h).hom.left) =
      affineChart (V.map (algebraMap R S)) ≫
        ((variableChangeCongrOverIso (W.map (algebraMap R S)) (V.map (algebraMap R S))
          (C.map σ.toRingHom) (coefficientEnd_variableChange_equation W S σ V C h)).hom.left ≫
            coefficientEndMorphism W S σ) := by
  have hl := square_comp (affineChart_coefficientEnd V S σ)
    (affineChart_variableChangeCongr (W.map (algebraMap R S)) (V.map (algebraMap R S)) C h)
  have hr := square_comp
    (affineChart_variableChangeCongr (W.map (algebraMap R S)) (V.map (algebraMap R S))
      (C.map σ.toRingHom) (coefficientEnd_variableChange_equation W S σ V C h))
    (affineChart_coefficientEnd W S σ)
  apply hl.trans
  apply Eq.trans _ hr.symm
  have hs := specMap_ringHom_square _ _ _ _
    (coefficientEnd_variableChange_affine W S σ V C h)
  exact congrArg (fun z => z ≫ affineChart (W.map (algebraMap R S))) hs

/-- Coefficient action conjugates coordinate changes on the glued cubic. -/
theorem coefficientEnd_variableChange :
    coefficientEndMorphism V S σ ≫
      (variableChangeCongrOverIso (W.map (algebraMap R S)) (V.map (algebraMap R S)) C h).hom.left =
      (variableChangeCongrOverIso (W.map (algebraMap R S)) (V.map (algebraMap R S))
        (C.map σ.toRingHom) (coefficientEnd_variableChange_equation W S σ V C h)).hom.left ≫
          coefficientEndMorphism W S σ := by
  apply affineChart_hom_ext (V.map (algebraMap R S)) (toBase (W.map (algebraMap R S)))
  · rw [Category.assoc, variableChangeCongr_toBase, coefficientEndMorphism_toBase,
      Category.assoc, coefficientEndMorphism_toBase, ← Category.assoc, variableChangeCongr_toBase]
  · exact coefficientEnd_variableChange_chart W S σ V C h


/-- Negating the quadratic root is the actual pulled-back covering involution. -/
theorem coefficientEnd_quadratic (d : Rˣ) :
    coefficientEndMorphism W (QuadraticEtaleRing d) (quadraticEtaleNeg d) ≫
      (baseChangeIso W (QuadraticEtaleRing d)).hom =
        (baseChangeIso W (QuadraticEtaleRing d)).hom ≫ quadraticPullbackSign d (toBase W) := by
  have hfst := quadraticPullbackSign_fst d (toBase W)
  have hsnd := quadraticPullbackSign_snd d (toBase W)
  dsimp only [quadraticEtaleCover] at hfst hsnd
  apply pullback.hom_ext
  · simp only [Category.assoc, baseChangeIso_hom_fst, hfst, coefficientEndMorphism_coefficient]
  · simp only [Category.assoc, baseChangeIso_hom_snd, hsnd,
      coefficientEndMorphism_toBase, quadraticEtaleSignMorphism]
    rw [← Category.assoc, baseChangeIso_hom_snd]

/-- The quadratic coefficient involution sends the distinguished root unit to its negative. -/
theorem quadraticEtaleNeg_unit_map (d : Rˣ) :
    Units.map (quadraticEtaleNeg d).toMonoidHom (quadraticEtaleUnit d) =
      -(quadraticEtaleUnit d) := by
  apply Units.ext
  exact quadraticEtaleNeg_unit d

end WeierstrassCurve.CubicCharts
