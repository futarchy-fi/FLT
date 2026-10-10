/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassProjectivePointComparison
public import FLT.Mazur.EllipticProjectiveBaseChange

/-!
# Naturality of the projective comparison under field extension

Extending projective coordinates agrees with precomposing the associated
scheme point by the spectrum map. The chart calculation works over arbitrary
coefficient algebras, before specializing to field-valued points.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve.Projective

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] (W : WeierstrassCurve R)

/-- Normalized chart evaluation commutes with every coefficient-preserving algebra map. -/
theorem integralChartPoint_natural (j : Fin 3) (v : Fin 3 → S)
    (hv : (W.map (algebraMap R S)).toProjective.Equation v) (hj : v j = 1)
    (f : S →ₐ[R] T) (hw : (W.map (algebraMap R T)).toProjective.Equation (f ∘ v))
    (hk : (f ∘ v) j = 1) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ integralChartPoint W j v hv hj =
      integralChartPoint W j (f ∘ v) hw hk := by
  rw [integralChartPoint, ← Category.assoc, ← Spec.map_comp, integralChartPoint]
  have he := congrArg AlgHom.toRingHom (evaluation_natural W j v hv hj f hw hk)
  exact congrArg (fun a => Spec.map (CommRingCat.ofHom a) ≫ integralCurveChart W j) he

variable {K L : Type u} [Field K] [Field L] [Algebra R K] [Algebra R L]

/-- Coefficient extension preserves the target equation literally. -/
theorem integralProjective_extension_equation (f : K →ₐ[R] L) :
    (W.map (algebraMap R K)).map f.toRingHom = W.map (algebraMap R L) := by
  ext <;> exact f.commutes _

/-- The classical point map attached to a coefficient-preserving field extension. -/
def integralProjectiveExtension (f : K →ₐ[R] L) :
    (W.map (algebraMap R K)).toProjective.Point →+
      (W.map (algebraMap R L)).toProjective.Point :=
  FLT.Mazur.extensionProjectiveHom _ f.toRingHom _ (integralProjective_extension_equation W f)

/-- The point comparison commutes with extension of the field of definition. -/
theorem projectiveToIntegral_natural (f : K →ₐ[R] L)
    (P : (W.map (algebraMap R K)).toProjective.Point) :
    (projectiveToIntegral W (integralProjectiveExtension W f P)).left =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ (projectiveToIntegral W P).left := by
  obtain ⟨j, v, hv, hj, he⟩ := exists_normalized_projective (W.map (algebraMap R K)) P
  have hw : (W.map (algebraMap R L)).toProjective.Equation (f ∘ v) := by
    have h := hv.map f.toRingHom
    change ((W.map (algebraMap R K)).map f.toRingHom).toProjective.Equation (f ∘ v) at h
    rw [integralProjective_extension_equation] at h
    exact h
  have hk : (f ∘ v) j = 1 := by simp [hj]
  have hc : (⟦f ∘ v⟧ : PointClass L) = (integralProjectiveExtension W f P).point := by
    change FLT.Mazur.extensionPointClass f.toRingHom ⟦v⟧ =
      FLT.Mazur.extensionPointClass f.toRingHom P.point
    rw [he]
  rw [projectiveToIntegral_chart W _ j _ hw hk hc,
    projectiveToIntegral_chart W P j v hv hj he, integralChartPoint_natural]

end FLT.Mazur.WeierstrassIntegralChart
