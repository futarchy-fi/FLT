/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveOriginalOpen
public import FLT.Mazur.WeierstrassDividedDepthBoundaryPullback

/-!
# Full unchanged principal opens at normalized divided depths

The actual successive Rees comparison is transported through the proved
coefficient normalization. The target inclusion retains that normalization,
so no equality of merely abstract localization schemes is used.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  {k : ℕ} (hπ : π ≠ 0) (d : Data W π k) (e : Data W π (k + 1))

/-- The actual preceding equation chart identified with its normalized depth datum. -/
def previousChartIso :
    Spec (.of (WeierstrassDilatation.Coordinate W (π ^ k)
      (π * e.b3) (π * e.b4) (π ^ 2 * e.b6))) ≅ chart d :=
  Scheme.Spec.mapIso (WeierstrassSuccessiveX.previousDepthEquiv π k hπ W
    d.b3 d.b4 d.b6 e.b3 e.b4 e.b6 d.factor3 d.factor4 d.factor6
    e.factor3 e.factor4 e.factor6).toRingEquiv.toCommRingCatIso.op

variable (f : WeierstrassDilatation.Coordinate W (π ^ k)
  (π * e.b3) (π * e.b4) (π ^ 2 * e.b6))
  (hf : f ∈ WeierstrassSuccessiveX.modificationCenter W (π ^ k) π e.b3 e.b4 e.b6)

/-- The unchanged original principal open as an open of the normalized target chart. -/
def originalTarget : Spec (.of (Localization.Away f)) ⟶ chart d :=
  PrincipalAffineRefinement.inclusion f ≫ (previousChartIso hπ d e).hom

instance originalTarget_isOpenImmersion : IsOpenImmersion (originalTarget hπ d e f) := by
  unfold originalTarget
  infer_instance

/-- The full local principal-open square after normalizing its target coefficients. -/
theorem localOriginal_isPullback :
    IsPullback (𝟙 _)
      (WeierstrassSuccessiveRees.originalOpen W (π ^ k) π e.b3 e.b4 e.b6 hπ f hf)
      (originalTarget hπ d e f) (localContraction hπ d e) := by
  apply (WeierstrassSuccessiveRees.originalOpen_isPullback
    W (π ^ k) π e.b3 e.b4 e.b6 hπ f hf).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (previousChartIso hπ d e)
  · simp
  · simp
  · simp [originalTarget]
  · rfl

end FLT.Mazur.WeierstrassDividedDepth
