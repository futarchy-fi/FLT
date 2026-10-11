/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothOriginalFiberLineParameters
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Fixed smooth translations recover every geometric fiber line

For the original proper smooth geometrically integral family over an affine
base, a fixed ample line restricts to an ample line on each geometric fiber.
The constructed ordered translation family recovers every line on every
such fiber, with the original total-space map and Picard class unchanged.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback OrderedCurvePower
variable {k : Type} [Field k] [IsAlgClosed k] {C X S : Scheme} [IsAffine S]
  {c : C ⟶ X} {q : C ⟶ Spec (.of k)} {f : X ⟶ S} {g : Spec (.of k) ⟶ S}
  (H : IsPullback c q f g) [IsProper f] [SmoothOfRelativeDimension 1 f]
  [GeometricallyIntegral f] {B : X.Modules} (hB : AmpleLineBundle B)
  {L : C.Modules} (hL : LocallyFreeRankOne L)

include hB hL in
/-- The fixed original smooth parameter family recovers every geometric-fiber line. -/
theorem exists_geometricFiber_smooth_line_parameter :
    ∃ (n d : ℕ) (p : Fin d → (Spec (.of k) ⟶ C)) (hp : ∀ i, p i ≫ q = 𝟙 _),
      0 < n ∧ Smooth (base f d) ∧
      Nonempty ((Scheme.Modules.pullback (fiberCurveMap H d p hp)).obj
        (translationLine f d (tensorPower B n)) ≅ L) := by
  let _ : GeometricallyIntegral q := MorphismProperty.of_isPullback H inferInstance
  let _ := GeometricallyIntegral.isIntegral_of_subsingleton q
  let _ : IsAffineHom c := MorphismProperty.of_isPullback H.flip inferInstance
  exact exists_smooth_originalFiber_line_parameter H hB.2.1 (hB.pullback_affine c) hL

include hB hL in
/-- The same fixed translations recover the exact original geometric-fiber Picard classes. -/
theorem exists_geometricFiber_smooth_picard_parameter :
    ∃ (n d : ℕ) (p : Fin d → (Spec (.of k) ⟶ C)) (hp : ∀ i, p i ≫ q = 𝟙 _),
      0 < n ∧ Smooth (base f d) ∧
      SchemePicard.pullback (fiberCurveMap H d p hp)
        (SchemePicard.mk (translationLine f d (tensorPower B n))
          (translationLine_rankOne f d (hB.2.1.tensorPower n))) = SchemePicard.mk L hL := by
  obtain ⟨n, d, p, hp, hn, hs, ⟨e⟩⟩ := exists_geometricFiber_smooth_line_parameter H hB hL
  refine ⟨n, d, p, hp, hn, hs, ?_⟩
  rw [SchemePicard.pullback_mk]
  exact SchemePicard.mk_eq_of_iso _ _ e

end FLT.Mazur.FCurve
