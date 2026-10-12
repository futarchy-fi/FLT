/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveBaseChangeIso

/-!
# Extending group comparisons across smooth generalized curves

For a smooth generalized curve the actual smooth inclusion is an isomorphism.
A group comparison therefore extends uniquely to the whole curve and its action.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E F : GeneralizedEllipticCurve S)

/-- Smoothness makes the specified smooth-group inclusion an isomorphism. -/
instance inclusion_isIso_of_smooth [Smooth E.curve.hom] : IsIso E.inclusion := by
  have hi : IsIso E.curve.hom.smoothLocus.ι := by
    rw [Scheme.Hom.smoothLocus_eq_top]
    exact E.curve.left.topIso.isIso_hom
  have : IsIso ((Over.forget S).map (curveSmoothInclusion E.curve)) := hi
  have : IsIso (curveSmoothInclusion E.curve) :=
    isIso_of_reflects_iso _ (Over.forget S)
  unfold inclusion
  infer_instance

variable [IsIso E.inclusion] [IsIso F.inclusion]
  (g : E.group ≅ F.group) [IsMonHom g.hom]

/-- Extend a smooth-group isomorphism using the original inclusions. -/
def smoothGroupCurveIso : E.curve ≅ F.curve :=
  (asIso E.inclusion).symm ≪≫ g ≪≫ asIso F.inclusion

omit [IsMonHom g.hom] in
/-- The extension preserves the actual smooth inclusions. -/
@[reassoc] theorem smoothGroupCurveIso_inclusion :
    E.inclusion ≫ (smoothGroupCurveIso E F g).hom = g.hom ≫ F.inclusion := by
  simp [smoothGroupCurveIso]

/-- The restriction identity forces equivariance of the extension on the whole curve. -/
theorem smoothGroupCurveIso_action :
    E.act ≫ (smoothGroupCurveIso E F g).hom =
      (g.hom ⊗ₘ (smoothGroupCurveIso E F g).hom) ≫ F.act := by
  apply (cancel_epi (E.group ◁ E.inclusion)).mp
  rw [← Category.assoc, E.action_inclusion, Category.assoc,
    smoothGroupCurveIso_inclusion]
  rw [← Category.assoc, ← id_tensorHom, tensorHom_comp_tensorHom_assoc]
  rw [smoothGroupCurveIso_inclusion, Category.id_comp]
  rw [IsMonHom.mul_hom g.hom, Category.assoc, ← F.action_inclusion]
  rw [← id_tensorHom, ← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]

/-- A group isomorphism of smooth generalized curves extends to the full DR objects. -/
def isoOfSmoothGroup : E ≅ F :=
  isoMk (smoothGroupCurveIso E F g) g (smoothGroupCurveIso_inclusion E F g)
    (smoothGroupCurveIso_action E F g)

/-- The full comparison retains exactly the prescribed group map. -/
theorem isoOfSmoothGroup_group : (isoOfSmoothGroup E F g).hom.group = g.hom := rfl

end FLT.Mazur.GeneralizedEllipticCurve
