/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationFunctionDescent
public import FLT.Mazur.SchemeOpenSectionDescent

/-!
# Invariant function descent on every invariant open

Restrict the source cover, the relation cover and the actual kernel-pair lift
to an invariant open. Effective descent then identifies the full invariant
rings on the restricted schemes; no relation is replaced by a diagonal.
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

include h₁ in
/-- The relation-cover preimage is exactly the upstairs relation open. -/
theorem relationCover_preimage : a ⁻¹ᵁ (g ⁻¹ᵁ W) = k ⁻¹ᵁ (p ⁻¹ᵁ W) := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h₁]

include h₁ h₂ hW in
/-- An invariant target open pulls back to an invariant source open. -/
theorem relationSource_preimage : a ⁻¹ᵁ (g ⁻¹ᵁ W) = b ⁻¹ᵁ (g ⁻¹ᵁ W) := by
  rw [relationCover_preimage g k h₁ W, hW, ← Scheme.Hom.comp_preimage, h₂,
    Scheme.Hom.comp_preimage]

/-- Restrict the actual relation comparison to the invariant relation domains. -/
def relationCoverOn : (a ⁻¹ᵁ (g ⁻¹ᵁ W)).toScheme ⟶ (p ⁻¹ᵁ W).toScheme :=
  k.resLE _ _ (relationCover_preimage g k h₁ W).le

/-- The restricted relation cover is still surjective. -/
instance relationCoverOn_surjective [Surjective k] :
    Surjective (relationCoverOn g k h₁ W) := by
  dsimp only [relationCoverOn]
  rw [k.resLE_congr _ rfl (relationCover_preimage g k h₁ W) (@Surjective),
    Scheme.Hom.resLE_eq_morphismRestrict]
  exact IsZariskiLocalAtTarget.restrict (P := @Surjective) inferInstance _

instance relationCoverOn_flat [Flat k] : Flat (relationCoverOn g k h₁ W) := by
  dsimp only [relationCoverOn]
  infer_instance

instance relationCoverOn_lfp [LocallyOfFinitePresentation k] :
    LocallyOfFinitePresentation (relationCoverOn g k h₁ W) :=
  IsZariskiLocalAtSource.resLE _ inferInstance

variable {r t : K ⟶ Y} (H : IsPullback r t g g)
  (l : K ⟶ B) (hl₁ : l ≫ a = r) (hl₂ : l ≫ b = t)

/-- The actual kernel-pair lift restricts to the upstairs relation open. -/
def relationKernelLiftOn : (r ⁻¹ᵁ (g ⁻¹ᵁ W)).toScheme ⟶
    (a ⁻¹ᵁ (g ⁻¹ᵁ W)).toScheme :=
  l.resLE _ _ (by rw [← Scheme.Hom.comp_preimage l a, hl₁])

/-- Both relation pullback squares remain commutative after restriction. -/
theorem relationCoverOn_fst :
    relationCoverOn g k h₁ W ≫ p.resLE W (p ⁻¹ᵁ W) le_rfl =
      a.resLE (g ⁻¹ᵁ W) _ le_rfl ≫ (g ∣_ W) := by
  dsimp only [relationCoverOn]
  rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_comp_resLE,
    Scheme.Hom.resLE_comp_resLE]
  congr 1

/-- The second square retains the invariant-domain equality. -/
theorem relationCoverOn_snd :
    relationCoverOn g k h₁ W ≫ q.resLE W (p ⁻¹ᵁ W) hW.le =
      b.resLE (g ⁻¹ᵁ W) _ (relationSource_preimage g k h₁ h₂ W hW).le ≫ (g ∣_ W) := by
  dsimp only [relationCoverOn]
  rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_comp_resLE,
    Scheme.Hom.resLE_comp_resLE]
  congr 1

/-- The restricted kernel lift retains its first endpoint. -/
theorem relationKernelLiftOn_fst :
    relationKernelLiftOn g W l hl₁ ≫ a.resLE (g ⁻¹ᵁ W) _ le_rfl =
      openKernelFst (a := r) (g := g) W := by
  dsimp only [relationKernelLiftOn, openKernelFst]
  rw [Scheme.Hom.resLE_comp_resLE]
  congr 1

include hl₂ in
/-- The restricted kernel lift retains its second endpoint. -/
theorem relationKernelLiftOn_snd :
    relationKernelLiftOn g W l hl₁ ≫
      b.resLE (g ⁻¹ᵁ W) _ (relationSource_preimage g k h₁ h₂ W hW).le =
        openKernelSnd H W := by
  dsimp only [relationKernelLiftOn, openKernelSnd]
  rw [Scheme.Hom.resLE_comp_resLE]
  congr 1

variable [Flat g] [Surjective g] [LocallyOfFinitePresentation g]
  [Flat k] [Surjective k] [LocallyOfFinitePresentation k]

/-- Invariant functions on every actual invariant open agree through the covering comparison. -/
def relationOpenFunctionRingEquiv :
    compatibleFunctions (p.resLE W (p ⁻¹ᵁ W) le_rfl) (q.resLE W (p ⁻¹ᵁ W) hW.le) ≃+*
      compatibleFunctions (a.resLE (g ⁻¹ᵁ W) _ le_rfl)
        (b.resLE (g ⁻¹ᵁ W) _ (relationSource_preimage g k h₁ h₂ W hW).le) := by
  let _ : Surjective (g ∣_ W) :=
    IsZariskiLocalAtTarget.restrict (P := @Surjective) inferInstance W
  exact relationFunctionRingEquiv (g ∣_ W) (relationCoverOn g k h₁ W)
    (relationCoverOn_fst g k h₁ W) (relationCoverOn_snd g k h₁ h₂ W hW)
    (openKernel_isPullback H W) (relationKernelLiftOn g W l hl₁)
    (relationKernelLiftOn_fst g W l hl₁) (relationKernelLiftOn_snd g k h₁ h₂ W hW H l hl₁ hl₂)

end FLT.Mazur.SchemeEffectiveEpiSections
