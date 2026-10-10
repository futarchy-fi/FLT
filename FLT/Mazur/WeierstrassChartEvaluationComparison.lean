/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassChartCrossComparison
public import FLT.Mazur.WeierstrassAdditionStructure

/-!
# Equality of normalized chart evaluations

Two coefficient-preserving chart evaluations define the same point of the
integral cubic exactly when their normalized homogeneous coordinates satisfy
the cross-coordinate identities. This compares actual scheme morphisms.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Global sections of a spectrum map are the original ring map through the canonical iso. -/
theorem specSectionHom_specMap {A : Type u} [CommRing A] (f : A →+* S) :
    specSectionHom (Spec.map (CommRingCat.ofHom f)) =
      (Scheme.ΓSpecIso (.of S)).inv.hom.comp f := by
  unfold specSectionHom
  rw [← Scheme.ΓSpecIso_inv_naturality]
  rfl

variable (W : WeierstrassCurve R)

/-- Equality on the integral cubic is exactly the normalized coordinate comparison. -/
theorem chart_algHom_global_eq_iff (j k : Fin 3)
    (f : Coordinate W j →ₐ[R] S) (g : Coordinate W k →ₐ[R] S) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ integralCurveChart W j =
        Spec.map (CommRingCat.ofHom g.toRingHom) ≫ integralCurveChart W k ↔
      ∀ i, f (coord W j i) = f (coord W j k) * g (coord W k i) := by
  constructor
  · intro h i
    have hc := chart_cross_of_global_eq W j k _ _ h i
    simp only [specSectionHom_specMap, RingHom.comp_apply, ← map_mul] at hc
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of S)).inv).1 hc
  · intro h
    apply global_eq_of_chart_cross W j k
    · exact (specAlgHom_structure f).trans (specAlgHom_structure g).symm
    · intro i
      simp only [specSectionHom_specMap, RingHom.comp_apply, ← map_mul]
      exact congrArg (Scheme.ΓSpecIso (.of S)).inv.hom (h i)

/-- A normalized homogeneous solution defines an actual point of the integral cubic. -/
def integralChartPoint (j : Fin 3) (v : Fin 3 → S)
    (hv : (W.map (algebraMap R S)).toProjective.Equation v) (hj : v j = 1) :
    Spec (.of S) ⟶ integralCurve W :=
  Spec.map (CommRingCat.ofHom (evaluation W j v hv hj).toRingHom) ≫ integralCurveChart W j

/-- A chart point has the prescribed coefficient map. -/
theorem integralChartPoint_structure (j : Fin 3) (v : Fin 3 → S)
    (hv : (W.map (algebraMap R S)).toProjective.Equation v) (hj : v j = 1) :
    integralChartPoint W j v hv hj ≫ integralCurveStructure W =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [integralChartPoint, Category.assoc, integralCurveChart_structure]
  exact specAlgHom_structure _

/-- Coordinate equations detect equality of two normalized chart points. -/
theorem integralChartPoint_eq_iff (j k : Fin 3) (v w : Fin 3 → S)
    (hv : (W.map (algebraMap R S)).toProjective.Equation v) (hj : v j = 1)
    (hw : (W.map (algebraMap R S)).toProjective.Equation w) (hk : w k = 1) :
    integralChartPoint W j v hv hj = integralChartPoint W k w hw hk ↔
      ∀ i, v i = v k * w i := by
  simpa only [integralChartPoint, evaluation_coord] using chart_algHom_global_eq_iff W j k
    (evaluation W j v hv hj) (evaluation W k w hw hk)

end FLT.Mazur.WeierstrassIntegralChart
