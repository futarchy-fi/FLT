/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperCoverImmersionCriterion

/-!
# Transporting immersed proper covers across a cartesian square

Base change of the cover and ambient scheme yields a cover of the original
scheme in a specified cartesian recovery square, with the same structure map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

/-- An immersed proper cover pulls back along a specified cartesian recovery square. -/
theorem exists_immersed_proper_cover_of_isPullback {X Y Z P S T : Scheme.{u}}
    (a : X ⟶ Y) (f : X ⟶ T) (q : Y ⟶ S) (b : T ⟶ S)
    (ha : IsPullback a f q b) (π : Z ⟶ Y) [IsProper π] [Surjective π]
    (p : P ⟶ S) [IsProper p] (h : Z ⟶ P) [IsImmersion h] [QuasiCompact h]
    (w : h ≫ p = π ≫ q) :
    ∃ (Z' P' : Scheme.{u}) (π' : Z' ⟶ X) (p' : P' ⟶ T) (h' : Z' ⟶ P'),
      IsProper π' ∧ Surjective π' ∧ IsProper p' ∧ IsImmersion h' ∧
        QuasiCompact h' ∧ h' ≫ p' = π' ≫ f := by
  let πb := immersionBaseChange (π ≫ q) q π rfl b
  let hb := immersionBaseChange (π ≫ q) p h w b
  let _ : IsProper πb := MorphismProperty.of_isPullback
    (immersionBaseChange_isPullback (π ≫ q) q π rfl b).flip inferInstance
  let _ : Surjective πb := MorphismProperty.of_isPullback
    (immersionBaseChange_isPullback (π ≫ q) q π rfl b).flip inferInstance
  let _ : IsImmersion hb := MorphismProperty.of_isPullback
    (immersionBaseChange_isPullback (π ≫ q) p h w b).flip inferInstance
  let _ : QuasiCompact hb := MorphismProperty.of_isPullback
    (immersionBaseChange_isPullback (π ≫ q) p h w b).flip inferInstance
  refine ⟨pullback (π ≫ q) b, pullback p b, πb ≫ ha.isoPullback.inv,
    pullback.snd p b, hb, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_⟩
  simp only [Category.assoc, ha.isoPullback_inv_snd, hb, πb, immersionBaseChange_snd]

end FLT.Mazur.Approximation
