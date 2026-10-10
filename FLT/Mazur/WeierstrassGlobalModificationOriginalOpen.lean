/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalModificationProper
public import FLT.Mazur.SchemeUnchangedOpen

/-!
# Entire unchanged principal opens in the global cubic modification

The full local principal-open pullbacks paste with the full original affine
chart pullback. This retains their original maps into the projective cubic.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassGlobalModification
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)
open WeierstrassIntegralChart
variable (f : Coordinate W 2) (hf : f ∈ WeierstrassDilatation.modificationCenter W s)

/-- The original principal open embedded in the entire modified projective cubic. -/
def originalOpen : Spec (.of (Localization.Away f)) ⟶ model W s b3 b4 b6 h3 h4 h6 hs :=
  WeierstrassModificationReesCoordinates.originalOpen W s b3 b4 b6 h3 h4 h6 hs f hf ≫
    localChart W s b3 b4 b6 h3 h4 h6 hs

instance originalOpen_isOpenImmersion :
    IsOpenImmersion (originalOpen W s b3 b4 b6 h3 h4 h6 hs f hf) := by
  unfold originalOpen
  infer_instance

/-- Every center principal open has its identity as full global contraction pullback. -/
theorem originalOpen_isPullback :
    IsPullback (𝟙 _) (originalOpen W s b3 b4 b6 h3 h4 h6 hs f hf)
      (PrincipalAffineRefinement.inclusion f ≫ integralCurveChart W 2)
      (contraction W s b3 b4 b6 h3 h4 h6 hs) :=
  (WeierstrassModificationReesCoordinates.originalOpen_isPullback
    W s b3 b4 b6 h3 h4 h6 hs f hf).paste_vert
      (local_isPullback W s b3 b4 b6 h3 h4 h6 hs)

/-- The actual unchanged principal open retains its original projective-cubic map. -/
@[reassoc] theorem originalOpen_contraction :
    originalOpen W s b3 b4 b6 h3 h4 h6 hs f hf ≫
        contraction W s b3 b4 b6 h3 h4 h6 hs =
      PrincipalAffineRefinement.inclusion f ≫ integralCurveChart W 2 := by
  simpa using (originalOpen_isPullback W s b3 b4 b6 h3 h4 h6 hs f hf).w.symm

include hf in
/-- Restriction of the entire global contraction to this original open is an isomorphism. -/
theorem originalOpen_restrict_isIso :
    IsIso (contraction W s b3 b4 b6 h3 h4 h6 hs ∣_
      (PrincipalAffineRefinement.inclusion f ≫ integralCurveChart W 2).opensRange) :=
  SchemeUnchangedOpen.isIso_of_identity_pullback _ _ _
    (originalOpen_isPullback W s b3 b4 b6 h3 h4 h6 hs f hf)

end FLT.Mazur.WeierstrassGlobalModification
