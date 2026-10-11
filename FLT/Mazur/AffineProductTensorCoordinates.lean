/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCartesianSectionPushout
public import FLT.Mazur.AffineBaseSectionAlgebra
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-!
# Tensor coordinates of actual affine products over the original ring

The coordinate ring of the product is the tensor product over R, using the
two original structural morphisms. The comparison preserves both projections.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
namespace FLT.Mazur.AffineProductTensorCoordinates
open Approximation
universe u
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R] (A V : Over (Spec (.of R)))
  [IsAffine A.left] [IsAffine V.left]
local notation "p" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "q" => Over.Hom.left (prod.snd : prod A V ⟶ V)
/-- The original structural algebra on source coefficients. -/
local instance sourceAlgebra : Algebra R Γ(A.left, ⊤) := affineBaseSectionAlgebra A.hom
/-- The original structural algebra on translation-base coefficients. -/
local instance translationAlgebra : Algebra R Γ(V.left, ⊤) := affineBaseSectionAlgebra V.hom

/-- The actual product sections are the pushout of the original R-coefficient maps. -/
theorem sections_isPushout :
    IsPushout (CommRingCat.ofHom (algebraMap R Γ(A.left, ⊤)))
      (CommRingCat.ofHom (algebraMap R Γ(V.left, ⊤))) (p).appTop (q).appTop := by
  have H : IsPushout A.hom.appTop V.hom.appTop (p).appTop (q).appTop :=
    isPushout_appTop_of_isPullback (show IsPullback p q A.hom V.hom from
      Over.isPullback_of_binaryFan_isLimit
        (BinaryFan.mk (prod.fst : prod A V ⟶ A) (prod.snd : prod A V ⟶ V)) (prodIsProd A V))
  apply H.of_iso' (Scheme.ΓSpecIso (.of R)).symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    rfl
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    rfl
  · simp
  · simp

/-- Multiplicative tensor coordinates for the original affine envelope. -/
def tensorIso : CommRingCat.of (Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤)) ≅
    Γ((prod A V).left, ⊤) :=
  (CommRingCat.isPushout_tensorProduct R Γ(A.left, ⊤) Γ(V.left, ⊤)).isoIsPushout
    _ _ (sections_isPushout A V)

/-- The first tensor coefficient pulls back along the original first projection. -/
theorem tensorIso_left (a : Γ(A.left, ⊤)) :
    (tensorIso A V).hom (a ⊗ₜ[R] 1) = (p).appTop a :=
  congrArg (fun h : Γ(A.left, ⊤) ⟶ Γ((prod A V).left, ⊤) ↦ h a)
    (IsPushout.inl_isoIsPushout_hom _ _
      (CommRingCat.isPushout_tensorProduct R Γ(A.left, ⊤) Γ(V.left, ⊤))
      (sections_isPushout A V))

/-- The second tensor coefficient pulls back along the independent second projection. -/
theorem tensorIso_right (b : Γ(V.left, ⊤)) :
    (tensorIso A V).hom (1 ⊗ₜ[R] b) = (q).appTop b :=
  congrArg (fun h : Γ(V.left, ⊤) ⟶ Γ((prod A V).left, ⊤) ↦ h b)
    (IsPushout.inr_isoIsPushout_hom _ _
      (CommRingCat.isPushout_tensorProduct R Γ(A.left, ⊤) Γ(V.left, ⊤))
      (sections_isPushout A V))

/-- Every pure tensor retains both original coefficient maps, multiplicatively. -/
theorem tensorIso_tmul (a : Γ(A.left, ⊤)) (b : Γ(V.left, ⊤)) :
    (tensorIso A V).hom (a ⊗ₜ[R] b) = (p).appTop a * (q).appTop b := by
  have h : a ⊗ₜ[R] b = (a ⊗ₜ[R] 1) * (1 ⊗ₜ[R] b) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h, map_mul, tensorIso_left, tensorIso_right]

end FLT.Mazur.AffineProductTensorCoordinates
