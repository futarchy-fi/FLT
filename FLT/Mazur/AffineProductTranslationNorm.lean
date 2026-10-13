/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineProductTensorCoordinates
public import FLT.Mazur.FiniteFreeTranslationNormNaturality

/-!
# Norms on actual affine translation envelopes

Use the original product section algebra and a genuine finite basis of the
translation algebra. Naturality under arbitrary source maps allows these
local constructions to be compared on affine open overlaps. Gluing on a
nonaffine full-envelope open remains a separate construction.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module TensorProduct
namespace FLT.Mazur.AffineProductTranslationNorm
open Approximation AffineProductTensorCoordinates FiniteFreeTranslationNorm
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type u} [CommRing R] (A B V : Over (Spec (.of R)))
  [IsAffine A.left] [IsAffine B.left] [IsAffine V.left]
/-- The original structural algebra on source sections. -/
local instance sourceAlgebra : Algebra R Γ(A.left, ⊤) := affineBaseSectionAlgebra A.hom
/-- The original structural algebra on refining source sections. -/
local instance targetAlgebra : Algebra R Γ(B.left, ⊤) := affineBaseSectionAlgebra B.hom
/-- The original translation section algebra. -/
local instance translationAlgebra : Algebra R Γ(V.left, ⊤) := affineBaseSectionAlgebra V.hom

/-- Original product sections commute with transport of both actual source coefficients. -/
theorem tensorIso_map (h : B ⟶ A) (x : Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤)) :
    (tensorIso B V).hom (Algebra.TensorProduct.map
      (affineBaseSectionHom B.hom A.hom h.left (Over.w h)) (AlgHom.id R _) x) =
      (prod.map h (𝟙 V)).left.appTop ((tensorIso A V).hom x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a s =>
    change (tensorIso B V).hom
      ((affineBaseSectionHom B.hom A.hom h.left (Over.w h) a) ⊗ₜ[R] s) =
        (prod.map h (𝟙 V)).left.appTop ((tensorIso A V).hom (a ⊗ₜ[R] s))
    rw [tensorIso_tmul, tensorIso_tmul, map_mul]
    apply congrArg₂ (· * ·)
    · change (prod.fst : prod B V ⟶ B).left.appTop (h.left.appTop a) = _
      have he := congrArg (fun t : prod B V ⟶ A ↦ t.left.appTop a)
        (prod.map_fst h (𝟙 V))
      exact he.symm
    · have he := congrArg (fun t : prod B V ⟶ V ↦ t.left.appTop s)
        (prod.map_snd h (𝟙 V))
      simpa only [Category.comp_id, Over.comp_left, Scheme.Hom.comp_appTop,
        CommRingCat.comp_apply] using he.symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The inverse tensor coordinate map also preserves the original envelope pullback. -/
theorem tensorIso_inv_map (h : B ⟶ A) (s : Γ((prod A V).left, ⊤)) :
    (tensorIso B V).inv ((prod.map h (𝟙 V)).left.appTop s) =
      Algebra.TensorProduct.map
        (affineBaseSectionHom B.hom A.hom h.left (Over.w h)) (AlgHom.id R _)
          ((tensorIso A V).inv s) := by
  apply (ConcreteCategory.bijective_of_isIso (tensorIso B V).hom).injective
  rw [Iso.inv_hom_id_apply, tensorIso_map, Iso.inv_hom_id_apply]

variable {ι : Type v} [Finite ι] (b : Basis ι R Γ(V.left, ⊤))

/-- The norm is taken in the actual original tensor envelope, with a finite translation basis. -/
def envelopeNorm (s : Γ((prod A V).left, ⊤)) : Γ(A.left, ⊤) :=
  let _ := Fintype.ofFinite ι
  let _ := Classical.decEq ι
  (Algebra.leftMulMatrix (b.baseChange Γ(A.left, ⊤)) ((tensorIso A V).inv s)).det

/-- The explicit matrix norm agrees with the algebra norm on this genuinely free envelope. -/
theorem envelopeNorm_eq_norm (s : Γ((prod A V).left, ⊤)) :
    envelopeNorm A V b s = Algebra.norm Γ(A.left, ⊤) ((tensorIso A V).inv s) := by
  classical
  let _ := Fintype.ofFinite ι
  exact (Algebra.norm_eq_matrix_det (b.baseChange Γ(A.left, ⊤)) _).symm

/-- Pulling back the envelope coefficient pulls back its norm on the source. -/
theorem envelopeNorm_natural (h : B ⟶ A) (s : Γ((prod A V).left, ⊤)) :
    envelopeNorm B V b ((prod.map h (𝟙 V)).left.appTop s) =
      h.left.appTop (envelopeNorm A V b s) := by
  rw [envelopeNorm_eq_norm, envelopeNorm_eq_norm, tensorIso_inv_map]
  exact norm_tensor_map b (affineBaseSectionHom B.hom A.hom h.left (Over.w h)) _

end FLT.Mazur.AffineProductTranslationNorm
