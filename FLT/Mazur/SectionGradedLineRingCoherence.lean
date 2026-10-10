/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedLineCoherence

/-!
# Functoriality of full section-ring pullback

The laws include equality transports between scheme maps, so they apply to
specified line systems whose scheme functor laws are propositional equalities.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules

namespace FLT.Mazur.SectionGradedLinePullback

open FCurve ModuleLineBundleTensorPullback SectionGradedMultiplication SectionGradedSum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X Y Z : Scheme}

/-- Identity pullback fixes the full ring of tensor-degree sections. -/
theorem ringHom_id (L : X.Modules) :
    ringHom (𝟙 X) ((pullbackId X).app L) = RingHom.id _ := by
  apply RingHom.ext
  intro s
  induction s using DirectSum.induction_on with
  | zero => exact map_zero _
  | of n s =>
    change ringHom (𝟙 X) ((pullbackId X).app L) (of L ⊤ n s) = of L ⊤ n s
    rw [ringHom_of, sectionMap_id]
    rfl
  | add s t hs ht => simp only [map_add, hs, ht]

/-- The full ring map agrees with two successive specified line pullbacks. -/
theorem ringHom_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    {L : Z.Modules} {M : Y.Modules} {N : X.Modules}
    (eg : (pullback g).obj L ≅ M) (ef : (pullback f).obj M ≅ N) :
    ringHom (f ≫ g) (compIso f g eg ef) = (ringHom f ef).comp (ringHom g eg) := by
  apply RingHom.ext
  intro s
  induction s using DirectSum.induction_on with
  | zero => simp
  | of n s =>
    change ringHom (f ≫ g) (compIso f g eg ef) (of L ⊤ n s) =
      ringHom f ef (ringHom g eg (of L ⊤ n s))
    rw [ringHom_of, ringHom_of, ringHom_of, sectionMap_comp]
    rfl
  | add s t hs ht => simp only [map_add, hs, ht]

/-- Equality transports of scheme maps preserve the actual homogeneous section maps. -/
theorem sectionMap_congr {f g : X ⟶ Y} (h : f = g)
    {L : Y.Modules} {M : X.Modules} (e : (pullback g).obj L ≅ M)
    (n : ℕ) (s : Piece L ⊤ n) :
    sectionMap f ((pullbackCongr h).app L ≪≫ e) n ⊤ s = sectionMap g e n ⊤ s := by
  subst g
  change sectionMap f (Iso.refl _ ≪≫ e) n ⊤ s = _
  rw [Iso.refl_trans]

/-- Equality transports of scheme maps preserve the full specified section-ring map. -/
theorem ringHom_congr {f g : X ⟶ Y} (h : f = g)
    {L : Y.Modules} {M : X.Modules} (e : (pullback g).obj L ≅ M) :
    ringHom f ((pullbackCongr h).app L ≪≫ e) = ringHom g e := by
  subst g
  change ringHom f (Iso.refl _ ≪≫ e) = _
  rw [Iso.refl_trans]

/-- The identity law retains a specified equality to the identity scheme morphism. -/
theorem ringHom_id_eq (f : X ⟶ X) (hf : f = 𝟙 X) (L : X.Modules) :
    ringHom f ((pullbackCongr hf).app L ≪≫ (pullbackId X).app L) = RingHom.id _ := by
  rw [ringHom_congr, ringHom_id]

/-- A coherent line system induces the full composition law, including map transports. -/
theorem ringHom_comp_eq (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (hk : k = f ≫ g)
    {L : Z.Modules} {M : Y.Modules} {N : X.Modules}
    (eg : (pullback g).obj L ≅ M) (ef : (pullback f).obj M ≅ N)
    (ek : (pullback k).obj L ≅ N)
    (he : (pullback f).mapIso eg ≪≫ ef =
      (pullbackComp f g).app L ≪≫ (pullbackCongr hk.symm).app L ≪≫ ek) :
    ringHom k ek = (ringHom f ef).comp (ringHom g eg) := by
  subst k
  change (pullback f).mapIso eg ≪≫ ef =
    (pullbackComp f g).app L ≪≫ (Iso.refl _ ≪≫ ek) at he
  rw [Iso.refl_trans] at he
  have hc : compIso f g eg ef = ek := by
    change ((pullbackComp f g).app L).symm ≪≫ ((pullback f).mapIso eg ≪≫ ef) = ek
    rw [he]
    simp
  rw [← hc, ringHom_comp]

end FLT.Mazur.SectionGradedLinePullback
