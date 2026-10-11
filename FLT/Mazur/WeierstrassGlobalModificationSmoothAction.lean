/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalModificationActionOverlap

/-!
# The smooth action map on the whole single-step modification

The constructed local lifts agree on every actual source overlap and hence
glue on the entire modified smooth-input product. This includes the full
exceptional locus and the original infinity input. Its contraction is the
original smooth action; identity and associativity are subsequent properties.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassGlobalModification

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)

/-- The actual smooth action map on the entire single-step modified cubic. -/
irreducible_def smoothAction : smoothActionProduct W s b3 b4 b6 h3 h4 h6 hs ⟶
    model W s b3 b4 b6 h3 h4 h6 hs :=
  (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).openCover.glueMorphisms
    (smoothActionLocal W s b3 b4 b6 h3 h4 h6 hs)
    (smoothActionLocal_overlap W s b3 b4 b6 h3 h4 h6 hs)

/-- On every full source member the glued map is precisely the constructed local lift. -/
@[reassoc] theorem smoothActionCover_action
    (i : (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).I₀) :
    (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).f i ≫
        smoothAction W s b3 b4 b6 h3 h4 h6 hs =
      smoothActionLocal W s b3 b4 b6 h3 h4 h6 hs i := by
  rw [smoothAction_def]
  exact (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).openCover.ι_glueMorphisms _ _ i

/-- The whole lifted action contracts to the actual original smooth action. -/
@[reassoc] theorem smoothAction_contraction :
    smoothAction W s b3 b4 b6 h3 h4 h6 hs ≫ contraction W s b3 b4 b6 h3 h4 h6 hs =
      smoothActionOriginal W s b3 b4 b6 h3 h4 h6 hs := by
  apply (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).openCover.hom_ext
  intro i
  simp only [Scheme.AffineOpenCover.openCover_f]
  rw [smoothActionCover_action_assoc, smoothActionLocal_contraction]

/-- The local constructions determine the whole lifted action without further gluing choices. -/
theorem smoothAction_eq_of_restrictions
    (f : smoothActionProduct W s b3 b4 b6 h3 h4 h6 hs ⟶
      model W s b3 b4 b6 h3 h4 h6 hs)
    (hf : ∀ i, (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).f i ≫ f =
      smoothActionLocal W s b3 b4 b6 h3 h4 h6 hs i) :
    f = smoothAction W s b3 b4 b6 h3 h4 h6 hs := by
  apply (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).openCover.hom_ext
  intro i
  simp only [Scheme.AffineOpenCover.openCover_f]
  rw [hf, smoothActionCover_action]

/-- Among all whole-source lifts of the original action, the constructed map is unique. -/
theorem smoothAction_eq_of_contraction
    (f : smoothActionProduct W s b3 b4 b6 h3 h4 h6 hs ⟶
      model W s b3 b4 b6 h3 h4 h6 hs)
    (hf : f ≫ contraction W s b3 b4 b6 h3 h4 h6 hs =
      smoothActionOriginal W s b3 b4 b6 h3 h4 h6 hs) :
    f = smoothAction W s b3 b4 b6 h3 h4 h6 hs := by
  apply smoothAction_eq_of_restrictions
  intro i
  have he := smoothActionLocal_flat_unique W s b3 b4 b6 h3 h4 h6 hs i (𝟙 _)
    ((smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).f i ≫ f) (by
      rw [Category.assoc, hf, Category.id_comp, smoothActionLocal_contraction])
  simpa only [Category.id_comp] using he

end FLT.Mazur.WeierstrassGlobalModification
