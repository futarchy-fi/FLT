/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperCoverImmersionCriterion

/-!
# Recovering a morphism between cartesian models

The literal base change of a model map is conjugate to the recovered map by
the two cartesian comparison isomorphisms. In particular, invertibility of
the recovered map implies invertibility of that literal base change.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

set_option backward.isDefEq.respectTransparency false

variable {P Q X Y T S : Scheme.{u}} {p : P ⟶ X} {q : P ⟶ T}
  {r : Q ⟶ Y} {s : Q ⟶ T} {f : X ⟶ S} {g : Y ⟶ S} {b : T ⟶ S}
  (hP : IsPullback p q f b) (hQ : IsPullback r s g b)
  (F : P ⟶ Q) (a : X ⟶ Y) (wa : a ≫ g = f)
  (wX : F ≫ r = p ≫ a) (wT : F ≫ s = q)

include hP hQ wX wT in
/-- The actual changed map is conjugation by the two cartesian recovery isomorphisms. -/
lemma cartesianMorphismRecovery_eq :
    immersionBaseChange f g a wa b = hP.isoPullback.inv ≫ F ≫ hQ.isoPullback.hom := by
  apply pullback.hom_ext
  · simp only [immersionBaseChange_fst, Category.assoc, IsPullback.isoPullback_hom_fst,
      wX]
    rw [← Category.assoc, IsPullback.isoPullback_inv_fst]
  · simp only [immersionBaseChange_snd, Category.assoc, IsPullback.isoPullback_hom_snd,
      wT, IsPullback.isoPullback_inv_snd]

include hP hQ wX wT in
/-- Invertibility of the recovered map is invertibility of the literal changed model map. -/
lemma cartesianMorphismRecovery_isIso [IsIso F] :
    IsIso (immersionBaseChange f g a wa b) := by
  rw [cartesianMorphismRecovery_eq hP hQ F a wa wX wT]
  infer_instance

end FLT.Mazur.Approximation
