/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicFieldAdditionTangent

/-! # Every field-valued scheme point is a classical cubic point -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable {K : Type u} [Field K] [Algebra R K]

theorem affineEvaluation_coordinates (f : Ring W false →ₐ[R] K) :
    affineEvaluation W (f (coord W false 0)) (f (coord W false 1))
      (chart_hom_equation W f) = f := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change affineEvaluation W (f (coord W false 0)) (f (coord W false 1))
    (chart_hom_equation W f) (coord W false i) = f (coord W false i)
  fin_cases i <;> simp

theorem affineFieldPoint_exists [W.IsElliptic] (f : Ring W false →ₐ[R] K) :
    ∃ P : (W.map (algebraMap R K)).toAffine.Point,
      fieldPointMorphism W P = Spec.map (CommRingCat.ofHom f.toRingHom) ≫ affineChart W := by
  let h := (Affine.equation_iff_nonsingular).mp (chart_hom_equation W f)
  refine ⟨.some (f (coord W false 0)) (f (coord W false 1)) h, ?_⟩
  change Spec.map (CommRingCat.ofHom
    (affineEvaluation W (f (coord W false 0)) (f (coord W false 1)) h.1).toRingHom) ≫
      affineChart W = _
  rw [affineEvaluation_coordinates]

theorem infinityFieldPoint_exists [W.IsElliptic] (f : Ring W true →ₐ[R] K) :
    ∃ P : (W.map (algebraMap R K)).toAffine.Point,
      fieldPointMorphism W P = Spec.map (CommRingCat.ofHom f.toRingHom) ≫ infinityChart W := by
  by_cases hv : f (coord W true 1) = 0
  · have he := eval₂_coord_equation W true f.toRingHom
    have hu : f (coord W true 0) = 0 := by
      apply eq_zero_of_pow_eq_zero (n := 3)
      simpa [equation, InfinityChart.equation, hv] using he
    have hf : f = (Algebra.ofId R K).comp (InfinityChart.origin W) := by
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro i
      change f (coord W true i) = algebraMap R K (InfinityChart.origin W (coord W true i))
      rw [infinity_origin_coord, map_zero]
      fin_cases i
      · exact hu
      · exact hv
    refine ⟨0, ?_⟩
    change Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
      (Spec.map (CommRingCat.ofHom (InfinityChart.origin W).toRingHom) ≫ infinityChart W) = _
    rw [← Category.assoc, ← Spec.map_comp, hf]
    rfl
  · let a : Overlap W true →ₐ[R] K :=
      IsLocalization.Away.liftAlgHom (coord W true 1) (f := f) (isUnit_iff_ne_zero.mpr hv)
    have ha (x : Ring W true) : a (algebraMap (Ring W true) (Overlap W true) x) = f x := by
      simp [a, IsLocalization.Away.liftAlgHom_apply]
    obtain ⟨P, hP⟩ := affineFieldPoint_exists W (a.comp (changeChart W true))
    refine ⟨P, hP.trans ?_⟩
    change Spec.map (CommRingCat.ofHom (changeChart W true).toRingHom ≫
      CommRingCat.ofHom a.toRingHom) ≫ affineChart W = _
    rw [Spec.map_comp, Category.assoc, changeChart_true_to_scheme]
    unfold overlapInclusion
    rw [← Category.assoc, ← Spec.map_comp]
    congr 1
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext ha

/-- Every morphism from a field spectrum over the coefficient base factors through
one of the two actual affine charts, with an algebra homomorphism on coordinates. -/
theorem fieldMorphism_factors_chart (f : Spec (.of K) ⟶ scheme W)
    (hbase : f ≫ toBase W = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃ (b : Bool) (a : Ring W b →ₐ[R] K),
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ sourceChart W b = f := by
  let x : Spec (.of K) := IsLocalRing.closedPoint K
  obtain ⟨b, z, hz⟩ := (sourceOpenCover W).exists_eq (f x)
  have hr : Set.range f ⊆ Set.range (sourceChart W b) := by
    rintro _ ⟨y, rfl⟩
    have hy : y = x := Subsingleton.elim _ _
    subst y
    exact ⟨z, hz⟩
  let g := IsOpenImmersion.lift (sourceChart W b) f hr
  have hg : g ≫ sourceChart W b = f := IsOpenImmersion.lift_fac _ _ hr
  obtain ⟨φ, hφ⟩ := Spec.map_surjective g
  have hb : Spec.map φ ≫ chartToBase W b =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [← sourceChart_toBase W b, ← Category.assoc, hφ, hg, hbase]
  have hc : CommRingCat.ofHom (algebraMap R (Ring W b)) ≫ φ =
      CommRingCat.ofHom (algebraMap R K) := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    exact hb
  let a : Ring W b →ₐ[R] K :=
    { φ.hom with
      commutes' := fun r ↦ congrArg (fun (ψ : CommRingCat.of R ⟶ CommRingCat.of K) ↦ ψ r) hc }
  refine ⟨b, a, ?_⟩
  change Spec.map φ ≫ sourceChart W b = f
  rw [hφ, hg]

/-- The classical-point encoding exhausts all field-valued points of the smooth cubic. -/
theorem fieldPointMorphism_surjective [W.IsElliptic]
    (f : Spec (.of K) ⟶ scheme W)
    (hbase : f ≫ toBase W = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃ P : (W.map (algebraMap R K)).toAffine.Point, fieldPointMorphism W P = f := by
  obtain ⟨b, a, ha⟩ := fieldMorphism_factors_chart W f hbase
  cases b
  · obtain ⟨P, hP⟩ := affineFieldPoint_exists W a
    exact ⟨P, hP.trans ha⟩
  · obtain ⟨P, hP⟩ := infinityFieldPoint_exists W a
    exact ⟨P, hP.trans ha⟩

end WeierstrassCurve.CubicCharts
