/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationAffineProper
public import FLT.Mazur.BlowupReesOriginalOpen

/-!
# Unchanged original principal opens in the actual equation modification

Transfer the entire Rees contraction preimage to the actual equation
modification. Any original center element gives an unchanged principal
open, with its original coordinate map and full cartesian square.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationReesCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)
  (f : WeierstrassIntegralChart.Coordinate W 2)
  (hf : f ∈ WeierstrassDilatation.modificationCenter W s)

/-- The actual equation modification contains the unchanged original principal open. -/
def originalOpen : Spec (.of (Localization.Away f)) ⟶
    WeierstrassModificationX.modification W s b3 b4 b6 :=
  BlowupRees.originalOpenInclusion (WeierstrassDilatation.modificationCenter W s) f hf ≫
    (modificationProjIso W s b3 b4 b6 h3 h4 h6 hs).inv

instance originalOpen_isOpenImmersion :
    IsOpenImmersion (originalOpen W s b3 b4 b6 h3 h4 h6 hs f hf) := by
  unfold originalOpen
  infer_instance

/-- The displayed unchanged open contracts by its original inclusion. -/
@[reassoc] theorem originalOpen_affineContraction :
    originalOpen W s b3 b4 b6 h3 h4 h6 hs f hf ≫
        WeierstrassModificationX.affineContraction W s b3 b4 b6 h3 h4 h6 =
      PrincipalAffineRefinement.inclusion f := by
  rw [originalOpen, Category.assoc,
    ← modificationProjIso_affineContraction W s b3 b4 b6 h3 h4 h6 hs,
    Iso.inv_hom_id_assoc, BlowupRees.originalOpenInclusion_contraction]

/-- The unchanged open is the entire pullback over the original principal open. -/
theorem originalOpen_isPullback :
    IsPullback (𝟙 _) (originalOpen W s b3 b4 b6 h3 h4 h6 hs f hf)
      (PrincipalAffineRefinement.inclusion f)
      (WeierstrassModificationX.affineContraction W s b3 b4 b6 h3 h4 h6) := by
  apply (BlowupRees.originalOpen_isPullback
    (WeierstrassDilatation.modificationCenter W s) f hf).of_iso
    (Iso.refl _) (Iso.refl _)
    (modificationProjIso W s b3 b4 b6 h3 h4 h6 hs).symm (Iso.refl _)
  · simp
  · simp [originalOpen]
  · simp
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
    rw [← modificationProjIso_affineContraction W s b3 b4 b6 h3 h4 h6 hs,
      Iso.inv_hom_id_assoc]

/-- Every point above the original principal open is in the displayed unchanged open. -/
theorem originalOpen_preimage :
    (WeierstrassModificationX.affineContraction W s b3 b4 b6 h3 h4 h6) ⁻¹'
        Set.range (PrincipalAffineRefinement.inclusion f) =
      Set.range (originalOpen W s b3 b4 b6 h3 h4 h6 hs f hf) := by
  have H := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (originalOpen_isPullback W s b3 b4 b6 h3 h4 h6 hs f hf) ⊤
  simpa using (congrArg SetLike.coe H).symm

end FLT.Mazur.WeierstrassModificationReesCoordinates
