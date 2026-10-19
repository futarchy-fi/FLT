/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveBaseChange
public import FLT.Mazur.OverCoverMonoidReflection

/-!
# Recovering full curve morphisms from an open base cover

The original curve and group maps form a generalized-curve morphism if they
recover such morphisms locally. Identity, multiplication, inclusion, and action
compatibility are proved by descent of their actual equations.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (C : S.OpenCover) {E F : GeneralizedEllipticCurve S}

/-- An open base cover detects the entire generalized-curve morphism. -/
theorem hom_ext_of_cover (f g : E ⟶ F)
    (h : ∀ i, baseChangeMap (C.f i) f = baseChangeMap (C.f i) g) : f = g := by
  apply forgetCurve.map_injective
  exact OverDirectedCoverGluing.hom_ext C f.curve g.curve
    (fun i ↦ congrArg Hom.curve (h i))

variable (c : E.curve ⟶ F.curve) (g : E.group ⟶ F.group)
  (a : ∀ i, E.baseChange (C.f i) ⟶ F.baseChange (C.f i))
  (hc : ∀ i, (Over.pullback (C.f i)).map c = (a i).curve)
  (hg : ∀ i, (Over.pullback (C.f i)).map g = (a i).group)

include hg in
/-- The recovered group map preserves its original group law. -/
theorem cover_group_isMonHom : IsMonHom g := by
  apply OverDirectedCoverGluing.isMonHom_of_cover C
  intro i
  rw [hg i]
  exact (a i).isMonHom

include hc hg in
/-- The recovered maps commute with the original smooth inclusions. -/
theorem cover_maps_inclusion : E.inclusion ≫ c = g ≫ F.inclusion := by
  apply OverDirectedCoverGluing.hom_ext C
  intro i
  simpa only [Functor.map_comp, hc i, hg i, baseChange_inclusion,
    pullbackInclusion] using (a i).inclusion

include hc hg in
/-- The recovered maps intertwine the original full-curve actions. -/
theorem cover_maps_action : E.act ≫ c = (g ⊗ₘ c) ≫ F.act := by
  apply OverDirectedCoverGluing.hom_ext C
  intro i
  let P := Over.pullback (C.f i)
  apply (cancel_epi (Functor.LaxMonoidal.μ P E.group E.curve)).mp
  rw [Functor.map_comp, Functor.map_comp, ← Category.assoc,
    ← Category.assoc, ← Functor.LaxMonoidal.μ_natural]
  simpa only [P, Category.assoc, baseChange, pullbackAction, hc i, hg i] using (a i).action

/-- Actual local recovery supplies a morphism in the full generalized-curve category. -/
def homOfCover : E ⟶ F where
  curve := c
  group := g
  isMonHom := cover_group_isMonHom C g a hg
  inclusion := cover_maps_inclusion C c g a hc hg
  action := cover_maps_action C c g a hc hg

/-- The constructed full morphism recovers every original local full morphism. -/
theorem homOfCover_map (i : C.I₀) :
    baseChangeMap (C.f i) (homOfCover C c g a hc hg) = a i :=
  Hom.ext (hc i) (hg i)

end FLT.Mazur.GeneralizedEllipticCurve
