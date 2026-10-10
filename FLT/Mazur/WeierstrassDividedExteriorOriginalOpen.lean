/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthOriginalOpen
public import FLT.Mazur.WeierstrassDividedExteriorProper

/-!
# Full unchanged center opens in an actual whole exterior step

The local principal-open pullbacks paste with the full divided-chart
pullback and transport through the existing reassociation isomorphism.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  {k : ℕ} (hπ : π ≠ 0) {d : Data W π k} (E : Exterior d) (e : Data W π (k + 1))
  (f : WeierstrassDilatation.Coordinate W (π ^ k)
    (π * e.b3) (π * e.b4) (π ^ 2 * e.b6))
  (hf : f ∈ WeierstrassSuccessiveX.modificationCenter W (π ^ k) π e.b3 e.b4 e.b6)

/-- The actual unchanged principal open embedded in the existing whole step. -/
def Exterior.stepOriginal : Spec (.of (Localization.Away f)) ⟶ (E.advance hπ e).whole :=
  WeierstrassSuccessiveRees.originalOpen W (π ^ k) π e.b3 e.b4 e.b6 hπ f hf ≫
    pushout.inr E.attach (localBoundary hπ d e) ≫ (E.advanceIso hπ e).inv

instance Exterior.stepOriginal_isOpenImmersion :
    IsOpenImmersion (E.stepOriginal hπ e f hf) := by
  unfold Exterior.stepOriginal
  infer_instance

/-- The full original principal-open pullback in the already constructed whole step. -/
theorem Exterior.stepOriginal_isPullback :
    IsPullback (𝟙 _) (E.stepOriginal hπ e f hf)
      (originalTarget hπ d e f ≫ E.dividedChart) (E.stepContraction hπ e) := by
  apply ((localOriginal_isPullback hπ d e f hf).paste_vert
    (E.localReplacement_divided_isPullback hπ e)).of_iso
      (Iso.refl _) (Iso.refl _) (E.advanceIso hπ e).symm (Iso.refl _)
  · simp
  · simp only [Iso.refl_hom, Iso.symm_hom, Category.id_comp, Category.assoc,
      Exterior.stepOriginal]
  · simp
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
    rw [← E.advanceIso_contraction hπ e, Iso.inv_hom_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth
