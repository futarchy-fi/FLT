/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.JointEnvelopeFullFiber

/-!
# Norm products from a finite joint translation cover

Each finite free translation subchart contributes its own determinant norm.
The product is nonzero exactly when the given section is nonzero on the
whole envelope fiber. No individual cover member is assumed Cartesian.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeTranslationNorm
open Approximation SchemeOpenEnvelope
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Finite products of actual regular functions intersect their nonvanishing domains. -/
theorem mem_basicOpen_finset_prod {I : Type*} (Y : Scheme) (c : I → Γ(Y, ⊤))
    (J : Finset I) (y : Y) :
    y ∈ Y.basicOpen (∏ i ∈ J, c i) ↔ ∀ i ∈ J, y ∈ Y.basicOpen (c i) := by
  classical
  induction J using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Scheme.basicOpen_one,
      TopologicalSpace.Opens.mem_top, Finset.notMem_empty, false_implies, implies_true]
  | @insert i J hi ih =>
    rw [Finset.prod_insert hi, Scheme.basicOpen_mul]
    simp only [TopologicalSpace.Opens.mem_inf, ih, Finset.mem_insert,
      forall_eq_or_imp]

variable {R : Type} [CommRing R] (B W : Over (Spec (.of R)))
  {I : Type} [Fintype I] (T : I → Over (Spec (.of R))) (t : ∀ i, T i ⟶ W)
  [∀ i, IsAffine (T i).left]
/-- Each cover member retains its own structural algebra. -/
local instance jointTranslationAlgebra (i : I) : Algebra R Γ((T i).left, ⊤) :=
  affineBaseSectionAlgebra (T i).hom
variable {ι : I → Type} [∀ i, Finite (ι i)]
  (b : ∀ i, Module.Basis (ι i) R Γ((T i).left, ⊤)) (s : Γ((prod B W).left, ⊤))

/-- The product of the genuine norms on the separate finite translation charts. -/
def jointTranslationNorm : Γ(B.left, ⊤) :=
  ∏ i, regularNorm B (T i) (b i) ((prod.map (𝟙 B) (t i)).left.appTop s)

/-- The norm product detects all fibers in every chosen translation chart. -/
theorem mem_basicOpen_jointTranslationNorm_iff (x : B.left) :
    x ∈ B.left.basicOpen (jointTranslationNorm B W T t b s) ↔
      ∀ i, x ∈ fullFiberLocus (prod.fst : prod B (T i) ⟶ B).left
        ((prod.map (𝟙 B) (t i)).left ⁻¹ᵁ (prod B W).left.basicOpen s) := by
  rw [jointTranslationNorm, mem_basicOpen_finset_prod]
  simp only [Finset.mem_univ, forall_const]
  apply forall_congr'
  intro i
  rw [Scheme.preimage_basicOpen_top, mem_fullFiberLocus, mem_basicOpen_regularNorm_iff]

variable (ht : ∀ w : W.left, ∃ i, ∃ z : (T i).left, (t i).left z = w)
include ht b

/-- Joint coverage turns the product support into the full original fiber condition. -/
theorem basicOpen_jointTranslationNorm_fullFiber :
    (B.left.basicOpen (jointTranslationNorm B W T t b s) : Set B.left) =
      fullFiberLocus (prod.fst : prod B W ⟶ B).left ((prod B W).left.basicOpen s) := by
  rw [fullFiberLocus_translationCover B W T t ht]
  ext x
  simp only [Set.mem_iInter]
  exact mem_basicOpen_jointTranslationNorm_iff B W T t b s x

omit [Fintype I] in
/-- The original full-fiber locus is open, although the original translation need not be finite. -/
theorem isOpen_fullFiber_of_jointTranslationCover [Finite I] :
    IsOpen (fullFiberLocus (prod.fst : prod B W ⟶ B).left
      ((prod B W).left.basicOpen s)) := by
  let _ := Fintype.ofFinite I
  rw [← basicOpen_jointTranslationNorm_fullFiber B W T t b s ht]
  exact (B.left.basicOpen _).isOpen

/-- The product constructs the maximal open full-fiber domain exactly. -/
theorem basicOpen_jointTranslationNorm_fullInterior :
    B.left.basicOpen (jointTranslationNorm B W T t b s) =
      fullFiberInterior (prod.fst : prod B W ⟶ B).left ((prod B W).left.basicOpen s) := by
  apply SetLike.coe_injective
  change _ = interior _
  rw [← basicOpen_jointTranslationNorm_fullFiber B W T t b s ht]
  exact (B.left.basicOpen _).isOpen.interior_eq.symm

end FLT.Mazur.SchemeTranslationNorm
