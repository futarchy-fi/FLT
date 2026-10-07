/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicVariableChangeGlobal
public import FLT.EllipticCurve.CubicGlobalIdentity
/-! # Coordinate changes as pointed isomorphisms of Weierstrass cubics

Identity and composition are checked on the schematically dense affine chart.
The inverse coordinate change gives the global inverse, and the regular
infinity neighborhood proves preservation of the distinguished section.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R]

/-- Transport the coordinate ring along equality of Weierstrass equations. -/
def chartRingCongr {W V : WeierstrassCurve R} (h : W = V) (b : Bool) :
    Ring W b ≃ₐ[R] Ring V b := by
  subst V
  exact AlgEquiv.refl

@[simp] theorem chartRingCongr_coord {W V : WeierstrassCurve R} (h : W = V)
    (b : Bool) (i : Fin 2) :
    chartRingCongr h b (coord W b i) = coord V b i := by
  subst V
  rfl

variable (W : WeierstrassCurve R) (C D : VariableChange R)

theorem variableChangeAffineMap_one :
    variableChangeAffineMap W 1 =
      (chartRingCongr (one_smul (VariableChange R) W).symm false).toAlgHom := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change variableChangeAffineMap W 1 (coord W false i) =
    chartRingCongr (one_smul (VariableChange R) W).symm false (coord W false i)
  rw [variableChangeAffineMap_coord, chartRingCongr_coord]
  fin_cases i <;> simp [variableChangeAffineCoords,
    show (1 : VariableChange R).u = 1 from rfl,
    show (1 : VariableChange R).r = 0 from rfl,
    show (1 : VariableChange R).s = 0 from rfl,
    show (1 : VariableChange R).t = 0 from rfl]

theorem variableChangeAffineMap_comp :
    (variableChangeAffineMap (D • W) C).comp (variableChangeAffineMap W D) =
      (chartRingCongr (mul_smul C D W) false).toAlgHom.comp
        (variableChangeAffineMap W (C * D)) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change variableChangeAffineMap (D • W) C (variableChangeAffineMap W D (coord W false i)) =
    chartRingCongr (mul_smul C D W) false
      (variableChangeAffineMap W (C * D) (coord W false i))
  rw [variableChangeAffineMap_coord, variableChangeAffineMap_coord]
  fin_cases i <;> simp [variableChangeAffineCoords, VariableChange.mul_def] <;> ring

theorem chartRingCongr_spec {W V : WeierstrassCurve R} (h : W = V) (b : Bool) :
    Spec.map (CommRingCat.ofHom (chartRingCongr h b).toAlgHom.toRingHom) =
      eqToHom (congrArg (fun E => chart E b) h.symm) := by
  subst V
  change Spec.map (𝟙 _) = 𝟙 _
  exact Spec.map_id _

theorem chart_eqToHom {W V : WeierstrassCurve R} (h : W = V) (b : Bool) :
    eqToHom (congrArg (fun E => chart E b) h) ≫ sourceChart V b =
      sourceChart W b ≫ eqToHom (congrArg scheme h) := by
  subst V
  simp

theorem eqToHom_toBase {W V : WeierstrassCurve R} (h : W = V) :
    eqToHom (congrArg scheme h) ≫ toBase V = toBase W := by
  subst V
  simp

private theorem specAlgHom_comp {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
    [Algebra R A] [Algebra R B] [Algebra R T] (f : B →ₐ[R] T) (g : A →ₐ[R] B) :
    Spec.map (CommRingCat.ofHom (f.comp g).toRingHom) =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.map (CommRingCat.ofHom g.toRingHom) :=
  Spec.map_comp (CommRingCat.ofHom g.toRingHom) (CommRingCat.ofHom f.toRingHom)

theorem variableChangeAffineMorphism_one :
    variableChangeAffineMorphism W 1 =
      eqToHom (congrArg (fun E => chart E false) (one_smul (VariableChange R) W)) := by
  unfold variableChangeAffineMorphism
  rw [variableChangeAffineMap_one]
  exact chartRingCongr_spec (one_smul (VariableChange R) W).symm false

theorem variableChangeAffineMorphism_comp :
    variableChangeAffineMorphism (D • W) C ≫ variableChangeAffineMorphism W D =
      eqToHom (congrArg (fun E => chart E false) (mul_smul C D W).symm) ≫
        variableChangeAffineMorphism W (C * D) := by
  have h := congrArg (fun f : Ring W false →ₐ[R] Ring (C • (D • W)) false =>
    Spec.map (CommRingCat.ofHom f.toRingHom)) (variableChangeAffineMap_comp W C D)
  simpa only [specAlgHom_comp, chartRingCongr_spec, variableChangeAffineMorphism] using h

theorem variableChange_one :
    variableChangeMorphism W 1 =
      eqToHom (congrArg scheme (one_smul (VariableChange R) W)) := by
  apply affineChart_hom_ext (1 • W) (toBase W)
  · exact (variableChange_toBase W 1).trans
      (eqToHom_toBase (one_smul (VariableChange R) W)).symm
  · rw [affineChart_variableChange, variableChangeAffineMorphism_one]
    exact chart_eqToHom (one_smul (VariableChange R) W) false

theorem variableChange_comp :
    variableChangeMorphism (D • W) C ≫ variableChangeMorphism W D =
      eqToHom (congrArg scheme (mul_smul C D W).symm) ≫
        variableChangeMorphism W (C * D) := by
  apply affineChart_hom_ext (C • (D • W)) (toBase W)
  · simp only [Category.assoc, variableChange_toBase]
    exact (eqToHom_toBase (mul_smul C D W).symm).symm
  · calc
      affineChart (C • (D • W)) ≫
          (variableChangeMorphism (D • W) C ≫ variableChangeMorphism W D) =
        (variableChangeAffineMorphism (D • W) C ≫ variableChangeAffineMorphism W D) ≫
          affineChart W := by
            simp only [affineChart_variableChange_assoc, affineChart_variableChange, Category.assoc]
      _ = (eqToHom (congrArg (fun E => chart E false) (mul_smul C D W).symm) ≫
          variableChangeAffineMorphism W (C * D)) ≫ affineChart W := by
            rw [variableChangeAffineMorphism_comp]
      _ = affineChart (C • (D • W)) ≫
          (eqToHom (congrArg scheme (mul_smul C D W).symm) ≫
            variableChangeMorphism W (C * D)) := by
            rw [Category.assoc, ← affineChart_variableChange, ← Category.assoc]
            simpa only [Category.assoc, sourceChart] using congrArg
              (fun f => f ≫ variableChangeMorphism W (C * D))
              (chart_eqToHom (mul_smul C D W).symm false)


theorem variableChange_congr {W V : WeierstrassCurve R} (h : W = V) (C : VariableChange R) :
    eqToHom (congrArg (fun E => scheme (C • E)) h) ≫ variableChangeMorphism V C =
      variableChangeMorphism W C ≫ eqToHom (congrArg scheme h) := by
  subst V
  simp

theorem variableChange_parameter_congr {C D : VariableChange R} (h : C = D) :
    variableChangeMorphism W C =
      eqToHom (congrArg (fun E : VariableChange R => scheme (E • W)) h) ≫
        variableChangeMorphism W D := by
  subst D
  simp

theorem variableChange_comp_unit (h : C * D = 1) :
    variableChangeMorphism (D • W) C ≫ variableChangeMorphism W D =
      eqToHom (congrArg scheme (show C • (D • W) = W by
        rw [← mul_smul, h, one_smul])) := by
  rw [variableChange_comp, variableChange_parameter_congr W h, variableChange_one]
  simp only [eqToHom_trans]

theorem variableChange_inv_comp :
    eqToHom (congrArg scheme (inv_smul_smul C W).symm) ≫
        variableChangeMorphism (C • W) C⁻¹ ≫ variableChangeMorphism W C = 𝟙 _ := by
  rw [variableChange_comp_unit W C⁻¹ C (inv_mul_cancel C)]
  exact eqToHom_trans _ _

theorem variableChange_comp_inv :
    variableChangeMorphism W C ≫
        eqToHom (congrArg scheme (inv_smul_smul C W).symm) ≫
          variableChangeMorphism (C • W) C⁻¹ = 𝟙 _ := by
  rw [← Category.assoc, ← variableChange_congr (inv_smul_smul C W).symm C,
    Category.assoc, variableChange_comp_unit (C • W) C C⁻¹ (mul_inv_cancel C)]
  exact eqToHom_trans _ _

/-- Every admissible coordinate change gives an isomorphism of the entire cubic. -/
def variableChangeIso : scheme (C • W) ≅ scheme W where
  hom := variableChangeMorphism W C
  inv := eqToHom (congrArg scheme (inv_smul_smul C W).symm) ≫
    variableChangeMorphism (C • W) C⁻¹
  hom_inv_id := variableChange_comp_inv W C
  inv_hom_id := by
    simpa only [Category.assoc] using variableChange_inv_comp W C

instance variableChange_isIso : IsIso (variableChangeMorphism W C) :=
  (variableChangeIso W C).isIso_hom


/-- The infinity section lies in the regular neighborhood of the coordinate change. -/
def variableChangeNeighborhoodOrigin : VariableChangeNeighborhood W C →ₐ[R] R :=
  IsLocalization.Away.liftAlgHom (variableChangeInfinityDenominator W C)
    (f := infinityOrigin (C • W)) (by
      simpa only [variableChangeInfinityDenominator, map_add, map_mul, map_pow,
        AlgHom.commutes, infinityOrigin_coord, mul_zero, add_zero, Algebra.algebraMap_self,
        RingHom.id_apply]
        using C.u.isUnit.pow 3)

@[simp] theorem variableChangeNeighborhoodOrigin_algebraMap (x : Ring (C • W) true) :
    variableChangeNeighborhoodOrigin W C
      (algebraMap (Ring (C • W) true) (VariableChangeNeighborhood W C) x) =
      infinityOrigin (C • W) x := by
  simp [variableChangeNeighborhoodOrigin, IsLocalization.Away.liftAlgHom_apply]

theorem variableChangeNeighborhoodOrigin_comp :
    (variableChangeNeighborhoodOrigin W C).comp (variableChangeInfinityMap W C) =
      infinityOrigin W := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change variableChangeNeighborhoodOrigin W C
      (variableChangeInfinityMap W C (coord W true i)) = infinityOrigin W (coord W true i)
  rw [variableChangeInfinityMap_coord, infinityOrigin_coord]
  fin_cases i <;>
    simp [variableChangeInfinityCoords]

/-- The global coordinate change preserves the distinguished point at infinity. -/
@[reassoc (attr := simp)] theorem infinity_variableChange :
    infinity (C • W) ≫ variableChangeMorphism W C = infinity W := by
  have hf :
      Spec.map (CommRingCat.ofHom (variableChangeNeighborhoodOrigin W C).toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap (Ring (C • W) true) (VariableChangeNeighborhood W C))) =
        InfinityChart.infinity (C • W) := by
    unfold InfinityChart.infinity
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact RingHom.ext (variableChangeNeighborhoodOrigin_algebraMap W C)
  have hg : Spec.map (CommRingCat.ofHom (variableChangeNeighborhoodOrigin W C).toRingHom) ≫
      variableChangeInfinityMorphism W C = InfinityChart.infinity W := by
    unfold variableChangeInfinityMorphism InfinityChart.infinity
    rw [← Spec.map_comp]
    exact congrArg (fun f : Ring W true →ₐ[R] R =>
      Spec.map (CommRingCat.ofHom f.toRingHom)) (variableChangeNeighborhoodOrigin_comp W C)
  change (InfinityChart.infinity (C • W) ≫ infinityChart (C • W)) ≫
    variableChangeMorphism W C = InfinityChart.infinity W ≫ infinityChart W
  rw [Category.assoc, infinityChart_variableChange, ← hf, Category.assoc,
    neighborhood_variableChangeInfinityGlued, ← Category.assoc, hg]

end WeierstrassCurve.CubicCharts


