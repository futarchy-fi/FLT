/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperStageResidueFiberLimit

/-!
# Projection identities for the proper-stage fiber system

The residue-fiber cone and its transitions recover the actual original
structure maps. These identities compare pullbacks of the specified stage
line, without assuming a cartesian recovery square for the original envelope.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  {S : Scheme.{u}} {D : I ⥤ Scheme.{u}}
  (t : D ⟶ (Functor.const I).obj S) (i : I)
  (c : Cone D) (b : c.pt ⟶ S) (hb : ∀ j, c.π.app j ≫ t.app j = b) (s : S)

omit [IsCofiltered I] in
/-- The fiber cone projection recovers the original limit projection on total spaces. -/
theorem properStageResidueFiberCone_projection (j : Over i) :
    (properStageResidueFiberCone t i c b hb s).π.app j ≫
        pullback.snd (S.fromSpecResidueField s) (t.app j.left) =
      b.fiberι s ≫ c.π.app j.left := by
  change ((pullbackSymmetry b (S.fromSpecResidueField s)).hom ≫
    (properStageBaseChangeCone t (S.fromSpecResidueField s) i c b hb).π.app j) ≫ _ = _
  have hw : (properStageBaseChangeCone t (S.fromSpecResidueField s) i c b hb).π.app j ≫
      pullback.snd (S.fromSpecResidueField s) (t.app j.left) =
        pullback.snd (S.fromSpecResidueField s) b ≫ c.π.app j.left :=
    (schemeBaseChangeCone_isPullback ((Over.forget i).whiskerLeft t)
      (S.fromSpecResidueField s) (c.whisker (Over.forget i)) b (fun k ↦ hb k.left) j).w
  rw [Category.assoc, hw, ← Category.assoc, pullbackSymmetry_hom_comp_snd]
  rfl

omit [IsCofiltered I] in
/-- A transition to the identity refinement recovers the prescribed stage morphism. -/
theorem properStageBaseChangeDiagram_to_identity {Y : Scheme.{u}} (q : Y ⟶ S)
    (j : Over i) (f : j ⟶ Over.mk (𝟙 i)) :
    (properStageBaseChangeDiagram t q i).map f ≫ pullback.snd q (t.app i) =
      pullback.snd q (t.app j.left) ≫ D.map j.hom := by
  have hf : f.left = j.hom := by simpa using Over.w f
  have hw : (properStageBaseChangeDiagram t q i).map f ≫ pullback.snd q (t.app i) =
      pullback.snd q (t.app j.left) ≫ D.map f.left :=
    (schemeBaseChangeProjection ((Over.forget i).whiskerLeft t) q).naturality f
  rw [hf] at hw
  exact hw

omit [IsCofiltered I] in
/-- Proper base-changed stages over a separated scheme are separated. -/
theorem properStageBaseChangeDiagram_isSeparated {Y : Scheme.{u}} [Y.IsSeparated]
    (q : Y ⟶ S) [∀ {j k} (f : j ⟶ k), IsClosedImmersion (D.map f)]
    [IsProper (t.app i)] (j : Over i) :
    ((properStageBaseChangeDiagram t q i).obj j).IsSeparated := by
  let _ : IsProper (pullback.fst q (t.app j.left)) :=
    properStageBaseChangeDiagram_isProper t q i j
  change (pullback q (t.app j.left)).IsSeparated
  exact ⟨by simpa only [terminal.comp_from] using
    (inferInstance : IsSeparated (pullback.fst q (t.app j.left) ≫ terminal.from Y))⟩

end FLT.Mazur.Approximation
