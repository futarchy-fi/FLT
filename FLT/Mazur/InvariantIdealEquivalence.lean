/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantIdealRelation
public import FLT.Mazur.EquivalenceRelationInvariantRestriction
public import FLT.Mazur.IdealSheafPowerPullback

/-!
# Full equivalence relations on invariant ideal powers

The entire first-endpoint pullback carries reflexivity, inversion and
composition. Every ideal power retains this relation scheme-theoretically;
no reduction or flatness of the closed inclusion is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.InvariantIdealRelation
set_option backward.isDefEq.respectTransparency false
variable {X D : Scheme.{0}} (I : X.IdealSheafData) {p q : D ⟶ X}
  (h : I.comap p = I.comap q) (e : CategoryTheory.EquivalenceRelation p q)

/-- The full relation restricts to the closed scheme defined by the unchanged ideal. -/
def equivalence : CategoryTheory.EquivalenceRelation
    (pullback.snd p I.subschemeι) (snd I p q h) :=
  EquivalenceRelationFiber.invariantRestrictionEquivalence e
    (IsPullback.of_hasPullback p I.subschemeι) (snd_ι I p q h).symm

include h in
/-- Exact invariance retains every power, including all infinitesimal stages. -/
theorem pow_invariant (n : ℕ) : (I ^ n).comap p = (I ^ n).comap q := by
  rw [IdealSheafPowerPullback.comap_pow, IdealSheafPowerPullback.comap_pow, h]

/-- The constructed full equivalence relation on each infinitesimal closed stage. -/
def powEquivalence (n : ℕ) : CategoryTheory.EquivalenceRelation
    (pullback.snd p (I ^ n).subschemeι)
    (snd (I ^ n) p q (pow_invariant I h n)) :=
  equivalence (I ^ n) (pow_invariant I h n) e

end FLT.Mazur.InvariantIdealRelation
