/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientOriginalHomDescent

/-!
# Descending compact opens of the original whole family

A compact open of the original family is the exact inverse image of a
compact open at a finite coefficient stage. The formula uses the original
recovery map and is suitable for descending neighborhoods of the marking.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.Approximation
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Every original compact open descends through its specified Cartesian model. -/
theorem exists_coefficient_original_open {A : Type u} [CommRing A]
    (R : Subalgebra ℤ A) [Algebra.FiniteType ℤ R]
    {X Y : Scheme.{u}} {r : X ⟶ Spec (.of A)} (p : Y ⟶ Spec (.of R))
    [QuasiCompact p] [LocallyOfFiniteType p] {a : X ⟶ Y}
    (h : IsPullback a r p (Spec.map (CommRingCat.ofHom R.val.toRingHom)))
    (U : X.Opens) (hU : IsCompact (U : Set X)) :
    ∃ (i : (CoefficientStage R)ᵒᵖ) (V : ((coefficientModelDiagram R p).obj i).Opens),
      IsCompact (V : Set ((coefficientModelDiagram R p).obj i)) ∧
      coefficientModelRecovery h i ⁻¹ᵁ V = U := by
  have (i : (CoefficientStage R)ᵒᵖ) :
      IsNoetherian ((coefficientModelDiagram R p).obj i) := coefficientModel_isNoetherian p i
  obtain ⟨i, V, hV, he⟩ := AlgebraicGeometry.exists_preimage_eq
    (coefficientModelDiagram R p) (coefficientModelCone R p) (coefficientModelIsLimit R p)
    (h.isoPullback.inv ⁻¹ᵁ U)
    (QuasiCompact.isCompact_preimage (f := h.isoPullback.inv) _ U.isOpen hU)
  refine ⟨i, V, hV, ?_⟩
  rw [← coefficientModelRecovery_comparison h i, Scheme.Hom.comp_preimage, he,
    ← Scheme.Hom.comp_preimage, Iso.hom_inv_id]
  exact Scheme.Hom.id_preimage U

end FLT.Mazur.Approximation
