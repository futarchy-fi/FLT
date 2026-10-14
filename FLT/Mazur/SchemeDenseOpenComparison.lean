/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Scheme comparison from a schematically dense quotient

A scheme map descending a schematically dominant source projection is an open
immersion when its composite to a separated model is an open immersion.
The comparison is an isomorphism over that original open, including nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeDenseOpenComparison
set_option backward.isDefEq.respectTransparency false
variable {A J T U : Scheme} (f : A ⟶ J) (e : A ⟶ U) (s : U ⟶ J)
  (r : J ⟶ T) (u : U ⟶ T) (he : e ≫ s = f) (hs : s ≫ r = u)

/-- The descended comparison as a section over the old coefficient open. -/
def lift : U ⟶ pullback r u := pullback.lift s (𝟙 U) (by simpa using hs)

@[reassoc]
theorem lift_fst : lift s r u hs ≫ pullback.fst r u = s := pullback.lift_fst _ _ _

@[reassoc]
theorem lift_snd : lift s r u hs ≫ pullback.snd r u = 𝟙 U := pullback.lift_snd _ _ _

variable [IsSchemeTheoreticallyDominant f] [QuasiCompact f]
  [IsSeparated r] [IsOpenImmersion u]

include he hs in
/-- Schematic dominance of the original source kills the section's entire ideal. -/
theorem lift_isIso : IsIso (lift s r u hs) := by
  have H : IsPullback (𝟙 A) (e ≫ lift s r u hs) f (pullback.fst r u) :=
    IsPullback.of_horiz_isIso_mono ⟨by simp only [Category.id_comp,
      Category.assoc, lift_fst, he]⟩
  let _ : IsSchemeTheoreticallyDominant (e ≫ lift s r u hs) :=
    IsSchemeTheoreticallyDominant.of_isPullback H
  let _ : IsClosedImmersion (lift s r u hs ≫ pullback.snd r u) := by
    rw [lift_snd]
    infer_instance
  let _ : IsClosedImmersion (lift s r u hs) :=
    IsClosedImmersion.of_comp (lift s r u hs) (pullback.snd r u)
  apply IsClosedImmersion.isIso_iff_ker_eq_bot.mpr
  exact le_bot_iff.mp ((e.le_ker_comp (lift s r u hs)).trans (by rw [Scheme.Hom.ker_eq_bot]))

include he hs in
/-- The descended quotient is the actual open of the joint scheme over the old open. -/
theorem isOpenImmersion : IsOpenImmersion s := by
  let _ := lift_isIso f e s r u he hs
  rw [← lift_fst s r u hs]
  infer_instance

end FLT.Mazur.SchemeDenseOpenComparison
