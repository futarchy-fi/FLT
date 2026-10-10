/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveReesProper
public import FLT.Mazur.BlowupReesOriginalOpen

/-!
# Unchanged principal opens of the actual successive modification

Transfer the entire Rees contraction preimage to the actual successive
modification. Any original center element gives an unchanged principal
open, with its original coordinate map and full cartesian square.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveRees
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R]
  (W : WeierstrassCurve R) (s π b3 b4 b6 : R) (hπ : π ≠ 0)
  (f : WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6))
  (hf : f ∈ WeierstrassSuccessiveX.modificationCenter W s π b3 b4 b6)

/-- The actual equation modification contains the unchanged original principal open. -/
def originalOpen : Spec (.of (Localization.Away f)) ⟶
    WeierstrassSuccessiveX.modification W s π b3 b4 b6 :=
  BlowupRees.originalOpenInclusion (WeierstrassSuccessiveX.modificationCenter W s π b3 b4 b6) f hf ≫
    (modificationProjIso W s π b3 b4 b6 hπ).inv

instance originalOpen_isOpenImmersion :
    IsOpenImmersion (originalOpen W s π b3 b4 b6 hπ f hf) := by
  unfold originalOpen
  infer_instance

/-- The displayed unchanged open contracts by its original inclusion. -/
@[reassoc] theorem originalOpen_contraction :
    originalOpen W s π b3 b4 b6 hπ f hf ≫
        WeierstrassSuccessiveX.contraction W s π b3 b4 b6 =
      PrincipalAffineRefinement.inclusion f := by
  rw [originalOpen, Category.assoc,
    ← modificationProjIso_contraction W s π b3 b4 b6 hπ,
    Iso.inv_hom_id_assoc, BlowupRees.originalOpenInclusion_contraction]

/-- The unchanged open is the entire pullback over the original principal open. -/
theorem originalOpen_isPullback :
    IsPullback (𝟙 _) (originalOpen W s π b3 b4 b6 hπ f hf)
      (PrincipalAffineRefinement.inclusion f)
      (WeierstrassSuccessiveX.contraction W s π b3 b4 b6) := by
  apply (BlowupRees.originalOpen_isPullback
    (WeierstrassSuccessiveX.modificationCenter W s π b3 b4 b6) f hf).of_iso
    (Iso.refl _) (Iso.refl _)
    (modificationProjIso W s π b3 b4 b6 hπ).symm (Iso.refl _)
  · simp
  · simp [originalOpen]
  · simp
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
    rw [← modificationProjIso_contraction W s π b3 b4 b6 hπ,
      Iso.inv_hom_id_assoc]

/-- Every point above the original principal open is in the displayed unchanged open. -/
theorem originalOpen_preimage :
    (WeierstrassSuccessiveX.contraction W s π b3 b4 b6) ⁻¹'
        Set.range (PrincipalAffineRefinement.inclusion f) =
      Set.range (originalOpen W s π b3 b4 b6 hπ f hf) := by
  have H := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (originalOpen_isPullback W s π b3 b4 b6 hπ f hf) ⊤
  simpa using (congrArg SetLike.coe H).symm

end FLT.Mazur.WeierstrassSuccessiveRees
