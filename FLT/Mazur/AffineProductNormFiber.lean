/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineProductTranslationNorm
public import FLT.Mazur.AffineSectionNormFiber
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Full-fiber nonvanishing of actual affine translation norms

Transport the tensor basis to the original product section algebra. The norm
then tests all points of the scheme fiber, including independent residue branches.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module TensorProduct
namespace FLT.Mazur.AffineProductTranslationNorm
open Approximation AffineProductTensorCoordinates
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type u} [CommRing R] (A V : Over (Spec (.of R)))
  [IsAffine A.left] [IsAffine V.left]
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
/-- The original source structural algebra. -/
local instance fiberSourceAlgebra : Algebra R Γ(A.left, ⊤) := affineBaseSectionAlgebra A.hom
/-- The original translation structural algebra. -/
local instance fiberTranslationAlgebra : Algebra R Γ(V.left, ⊤) := affineBaseSectionAlgebra V.hom
/-- Product sections with scalars pulled along the first projection. -/
local instance fiberProductAlgebra : Algebra Γ(A.left, ⊤) Γ((prod A V).left, ⊤) :=
  (π).appTop.hom.toAlgebra

/-- Tensor coordinates preserve the actual first-projection algebra structure. -/
def tensorSectionAlgEquiv :
    (Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤)) ≃ₐ[Γ(A.left, ⊤)] Γ((prod A V).left, ⊤) :=
  { (tensorIso A V).commRingCatIsoToRingEquiv with
    commutes' := tensorIso_left A V }

variable {ι : Type v} [Finite ι] (b : Basis ι R Γ(V.left, ⊤))

/-- The original product has a finite basis over its actual source sections. -/
def envelopeSectionBasis : Basis ι Γ(A.left, ⊤) Γ((prod A V).left, ⊤) :=
  (b.baseChange Γ(A.left, ⊤)).map (tensorSectionAlgEquiv A V).toLinearEquiv

/-- The matrix construction computes the norm on the actual product sections. -/
theorem envelopeNorm_eq_section_norm (s : Γ((prod A V).left, ⊤)) :
    envelopeNorm A V b s = Algebra.norm Γ(A.left, ⊤) s := by
  rw [envelopeNorm_eq_norm]
  have h := Algebra.norm_eq_of_algEquiv (tensorSectionAlgEquiv A V)
    ((tensorIso A V).inv s)
  change Algebra.norm Γ(A.left, ⊤) ((tensorIso A V).hom ((tensorIso A V).inv s)) = _ at h
  rw [Iso.inv_hom_id_apply] at h
  exact h.symm

/-- The actual affine envelope norm is nonzero exactly on complete nonvanishing fibers. -/
theorem mem_basicOpen_envelopeNorm_iff (s : Γ((prod A V).left, ⊤)) (x : A.left) :
    x ∈ A.left.basicOpen (envelopeNorm A V b s) ↔
      ∀ z : (prod A V).left, (π) z = x → z ∈ (prod A V).left.basicOpen s := by
  let _ : IsAffine (prod A V).left := IsAffine.of_isIso (Over.prodLeftIsoPullback A V).hom
  rw [envelopeNorm_eq_section_norm]
  exact AffineSectionNormFiber.mem_basicOpen_norm_iff π (envelopeSectionBasis A V b) s x

end FLT.Mazur.AffineProductTranslationNorm
