/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationOpenInvariantRings

/-!
# Invariant descent when the covers are surjective only over the chosen open

The common source need not cover the entire original source. It suffices that
its restriction covers the chosen invariant open and that the relation map
covers the corresponding original relation open.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeEffectiveEpiSections
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y A B K : Scheme.{u}} {p q : A ⟶ X} {a b : B ⟶ Y}
  (g : Y ⟶ X) (k : B ⟶ A)
  (h₁ : k ≫ p = a ≫ g) (h₂ : k ≫ q = b ≫ g)
  (W : X.Opens) (hW : p ⁻¹ᵁ W = q ⁻¹ᵁ W)
  {r t : K ⟶ Y} (H : IsPullback r t g g)
  (l : K ⟶ B) (hl₁ : l ≫ a = r) (hl₂ : l ≫ b = t)
  [Flat g] [LocallyOfFinitePresentation g] [Flat k] [LocallyOfFinitePresentation k]
  [Surjective (g ∣_ W)] [Surjective (k ∣_ (p ⁻¹ᵁ W))]

omit [Flat g] [LocallyOfFinitePresentation g] [Flat k]
  [LocallyOfFinitePresentation k] [Surjective (g ∣_ W)] in
/-- The relation comparison on the actual invariant domain is a surjection. -/
theorem relationCoverOn_surjective_of_restrict : Surjective (relationCoverOn g k h₁ W) := by
  dsimp only [relationCoverOn]
  rw [k.resLE_congr _ rfl (relationCover_preimage g k h₁ W) (@Surjective),
    Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

/-- Local covering suffices for descent of the actual original open invariant rings. -/
def relationLocalInvariantRingEquiv : relationOpenFunctions p q W hW ≃+*
    relationOpenFunctions a b (g ⁻¹ᵁ W) (relationSource_preimage g k h₁ h₂ W hW) := by
  let _ := relationCoverOn_surjective_of_restrict g k h₁ W
  exact (relationOpenCoordinates p q W hW).trans
    ((relationFunctionRingEquiv (g ∣_ W) (relationCoverOn g k h₁ W)
      (relationCoverOn_fst g k h₁ W) (relationCoverOn_snd g k h₁ h₂ W hW)
      (openKernel_isPullback H W) (relationKernelLiftOn g W l hl₁)
      (relationKernelLiftOn_fst g W l hl₁)
      (relationKernelLiftOn_snd g k h₁ h₂ W hW H l hl₁ hl₂)).trans
        (relationOpenCoordinates a b _ _).symm)

/-- The local comparison is still the actual original section pullback. -/
theorem relationLocalInvariantRingEquiv_val (s : relationOpenFunctions p q W hW) :
    (relationLocalInvariantRingEquiv g k h₁ h₂ W hW H l hl₁ hl₂ s).val =
      g.app W s.val := by
  apply (g ⁻¹ᵁ W).topIso.symm.commRingCatIsoToRingEquiv.injective
  change ((relationOpenCoordinates a b _ _)
    ((relationLocalInvariantRingEquiv g k h₁ h₂ W hW H l hl₁ hl₂) s)).val = _
  dsimp only [relationLocalInvariantRingEquiv, RingEquiv.trans_apply]
  rw [RingEquiv.apply_symm_apply]
  change (g ∣_ W).appTop (W.topIso.inv s.val) = _
  rw [← Scheme.Hom.resLE_eq_morphismRestrict, resLE_appTop_coordinates]
  simp only [Scheme.Hom.appLE_eq_app, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  rfl

end FLT.Mazur.SchemeEffectiveEpiSections
