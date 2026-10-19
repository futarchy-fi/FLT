/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalFiniteSmoothEmbedding
public import FLT.Mazur.WeierstrassGenericClosureSmoothDensity
public import FLT.Mazur.WeierstrassGenericKernelRecovery

/-!
# The original generic cubic inside every divided model

The retained smooth embedding gives a concrete map from the original generic
cubic. Its contraction and base square identify the entire generic fiber,
including when the integral cubic has bad reduction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R K : Type} [CommRing R] [IsDomain R] [IsBezout R]
  [Field K] [Algebra R K]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  (hΔ : IsUnit (W.map (algebraMap R K)).Δ)

/-- Insert the actual original generic cubic into the full divided model. -/
def finiteGlobalGenericCurve : integralCurve (W.map (algebraMap R K)) ⟶
    finiteGlobalModel hπ data j hj :=
  genericCurveToIntegralSmooth W hΔ ≫ finiteGlobalSmoothEmbedding hπ data j hj

/-- Contraction recovers exactly the original coefficient projection. -/
@[reassoc] theorem finiteGlobalGenericCurve_contraction :
    finiteGlobalGenericCurve hπ data j hj hΔ ≫ finiteGlobalContraction hπ data j hj =
      integralCoefficientMorphism W := by
  rw [finiteGlobalGenericCurve, Category.assoc, finiteGlobalSmoothEmbedding_contraction,
    genericCurveToIntegralSmooth_inclusion]

/-- The generic cubic is the entire inverse image under contraction. -/
theorem finiteGlobalGenericCurve_contraction_isPullback :
    IsPullback (𝟙 _) (finiteGlobalGenericCurve hπ data j hj hΔ)
      (integralCoefficientMorphism W) (finiteGlobalContraction hπ data j hj) := by
  have ht : IsPullback (𝟙 _) (genericCurveToIntegralSmooth W hΔ)
      (genericCurveToIntegralSmooth W hΔ) (𝟙 _) :=
    IsPullback.of_horiz_isIso_mono ⟨by simp only [Category.id_comp, Category.comp_id]⟩
  simpa only [genericCurveToIntegralSmooth_inclusion, finiteGlobalGenericCurve] using
    ht.paste_vert (finiteGlobalSmoothEmbedding_isPullback hπ data j hj)

/-- The actual original generic cubic is the generic fiber over the original base. -/
theorem finiteGlobalGenericCurve_isPullback :
    IsPullback (finiteGlobalGenericCurve hπ data j hj hΔ)
      (integralCurveStructure (W.map (algebraMap R K))) (finiteGlobalStructure hπ data j hj)
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  simpa only [Category.id_comp, finiteGlobalStructure] using
    (finiteGlobalGenericCurve_contraction_isPullback hπ data j hj hΔ).flip.paste_vert
      (integralCoefficient_isPullback W)

/-- Retain the exact original generic structure map. -/
@[reassoc] theorem finiteGlobalGenericCurve_structure :
    finiteGlobalGenericCurve hπ data j hj hΔ ≫ finiteGlobalStructure hπ data j hj =
      integralCurveStructure (W.map (algebraMap R K)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K)) :=
  (finiteGlobalGenericCurve_isPullback hπ data j hj hΔ).w

variable [IsFractionRing R K]

instance finiteGlobalGenericCurve_flat : Flat (finiteGlobalGenericCurve hπ data j hj hΔ) :=
  MorphismProperty.of_isPullback
    (finiteGlobalGenericCurve_contraction_isPullback hπ data j hj hΔ)
    (inferInstanceAs (Flat (integralCoefficientMorphism (S := K) W)))

instance finiteGlobalGenericCurve_mono : Mono (finiteGlobalGenericCurve hπ data j hj hΔ) :=
  (finiteGlobalGenericCurve_contraction_isPullback hπ data j hj hΔ).mono_snd_of_mono

instance finiteGlobalGenericCurve_quasiCompact :
    QuasiCompact (finiteGlobalGenericCurve hπ data j hj hΔ) :=
  MorphismProperty.of_isPullback (finiteGlobalGenericCurve_isPullback hπ data j hj hΔ).flip
    (inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R K)))))

omit [IsFractionRing R K] in
/-- Successive divided models retain the very same original generic cubic. -/
@[reassoc] theorem finiteGlobalGenericCurve_step (hnext : j + 1 ≤ n) :
    finiteGlobalGenericCurve hπ data (j + 1) hnext hΔ ≫ finiteGlobalStep hπ data j hnext =
      finiteGlobalGenericCurve hπ data j (Nat.le_of_succ_le hnext) hΔ := by
  rw [finiteGlobalGenericCurve, Category.assoc, finiteGlobalSmoothEmbedding_step]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
