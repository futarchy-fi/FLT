/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassChartEvaluationComparison

/-!
# Every field-valued integral cubic point has normalized coordinates

The spectrum of a field has one point, so every morphism into the integral
cubic factors through one of its actual affine charts. The factorization over
the coefficient spectrum recovers a coefficient-preserving chart evaluation.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
variable (W : WeierstrassCurve R)

omit [Algebra R K] in
/-- A field-valued morphism factors through one actual normalized chart. -/
theorem exists_field_chart (p : Spec (.of K) ⟶ integralCurve W) :
    ∃ j : Fin 3, ∃ f : Spec (.of K) ⟶ chartScheme W j,
      f ≫ integralCurveChart W j = p := by
  let x : Spec (.of K) := ⟨⊥, inferInstance⟩
  obtain ⟨j, y, hy⟩ := integralCurveChart_cover W (p x)
  have hr : Set.range p ⊆ Set.range (integralCurveChart W j) := by
    rintro _ ⟨z, rfl⟩
    exact ⟨y, hy.trans (congrArg p (Subsingleton.elim x z))⟩
  exact ⟨j, IsOpenImmersion.lift (integralCurveChart W j) p hr,
    IsOpenImmersion.lift_fac _ _ _⟩

/-- A chart factorization over the coefficient spectrum recovers an algebra map. -/
def fieldChartAlgHom (j : Fin 3) (f : Spec (.of K) ⟶ chartScheme W j)
    (hf : f ≫ chartStructure W j = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    Coordinate W j →ₐ[R] K := by
  refine { (Spec.preimage f).hom with commutes' := ?_ }
  intro r
  have he : Spec.map (CommRingCat.ofHom
      ((Spec.preimage f).hom.comp (algebraMap R (Coordinate W j)))) =
        Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [show CommRingCat.ofHom ((Spec.preimage f).hom.comp
      (algebraMap R (Coordinate W j))) =
        CommRingCat.ofHom (algebraMap R (Coordinate W j)) ≫ Spec.preimage f from rfl,
      Spec.map_comp, Spec.map_preimage]
    exact hf
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (Spec.map_injective he)) r

/-- The recovered chart algebra map gives back the entire chart morphism. -/
theorem fieldChartAlgHom_spec (j : Fin 3) (f : Spec (.of K) ⟶ chartScheme W j)
    (hf : f ≫ chartStructure W j = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    Spec.map (CommRingCat.ofHom (fieldChartAlgHom W j f hf).toRingHom) = f :=
  Spec.map_preimage f

/-- Every coefficient-preserving chart map gives a normalized homogeneous solution. -/
theorem chartAlgHom_equation {S : Type u} [CommRing S] [Algebra R S]
    (j : Fin 3) (f : Coordinate W j →ₐ[R] S) :
    (W.map (algebraMap R S)).toProjective.Equation (fun i => f (coord W j i)) := by
  have h := (coord_equation W j).map f.toRingHom
  change ((W.map (algebraMap R (Coordinate W j))).map f.toRingHom).toProjective.Equation
    (fun i => f (coord W j i)) at h
  have he : (W.map (algebraMap R (Coordinate W j))).map f.toRingHom =
      W.map (algebraMap R S) := by
    ext <;> exact f.commutes _
  rw [he] at h
  exact h

/-- The chart evaluation recovered from its coordinates is the original algebra map. -/
theorem evaluation_chartAlgHom {S : Type u} [CommRing S] [Algebra R S]
    (j : Fin 3) (f : Coordinate W j →ₐ[R] S) :
    evaluation W j (fun i => f (coord W j i)) (chartAlgHom_equation W j f)
      (by simp) = f := by
  apply hom_ext
  intro i
  exact evaluation_coord W j _ _ _ i

/-- Every field-valued point over the base is an actual normalized chart evaluation. -/
theorem exists_integralChartPoint (p : Spec (.of K) ⟶ integralCurve W)
    (hp : p ≫ integralCurveStructure W = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃ (j : Fin 3) (v : Fin 3 → K)
      (hv : (W.map (algebraMap R K)).toProjective.Equation v) (hj : v j = 1),
      integralChartPoint W j v hv hj = p := by
  obtain ⟨j, f, hf⟩ := exists_field_chart W p
  have hb : f ≫ chartStructure W j = Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [← integralCurveChart_structure, ← Category.assoc, hf, hp]
  let a := fieldChartAlgHom W j f hb
  refine ⟨j, fun i => a (coord W j i), chartAlgHom_equation W j a, by simp, ?_⟩
  rw [integralChartPoint, evaluation_chartAlgHom, fieldChartAlgHom_spec, hf]

end FLT.Mazur.WeierstrassIntegralChart
