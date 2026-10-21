/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupPresentationRecovery

/-!
# Comparing full subgroup maps through a common presentation

Two independently obtained presentation identities determine a comparison
built by flattening one pullback and expanding the other.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
variable {S : Scheme} {n : ℕ} {E F G D K : GeneralizedEllipticCurve S}
  {A : E.FiniteSubgroup n} {B : F.FiniteSubgroup n} {C : G.FiniteSubgroup n}
  {J : D.FiniteSubgroup n} {L : K.FiniteSubgroup n}

/-- Two commuting presentation squares determine the full comparison between their sources. -/
theorem CompatibleIso.compare_presentation_square
    (a : CompatibleIso A B) (b : CompatibleIso B C) (c : CompatibleIso A J)
    (d : CompatibleIso J C) (e : CompatibleIso J L) (f : CompatibleIso A L)
    (hab : a.trans b = c.trans d) (hfe : f = c.trans e) :
    (a.trans b).trans (d.symm.trans e) = f := by
  rw [hab, CompatibleIso.trans_assoc, ← CompatibleIso.trans_assoc d,
    CompatibleIso.trans_symm, CompatibleIso.refl_trans, hfe]

/-- Flattening one comparison and expanding another recovers the original compatible map. -/
theorem CompatibleIso.compare_presentation_square_cancel
    (a : CompatibleIso A B) (b : CompatibleIso B C) (c : CompatibleIso A J)
    (d : CompatibleIso J C) (e : CompatibleIso J L)
    {N : GeneralizedEllipticCurve S} {M : N.FiniteSubgroup n}
    (f : CompatibleIso A M) (k : CompatibleIso M L)
    (hab : a.trans b = c.trans d) (hfk : f.trans k = c.trans e) :
    (a.trans b).trans (d.symm.trans (e.trans k.symm)) = f := by
  rw [hab, CompatibleIso.trans_assoc, ← CompatibleIso.trans_assoc d,
    CompatibleIso.trans_symm, CompatibleIso.refl_trans, ← CompatibleIso.trans_assoc,
    ← hfk, CompatibleIso.trans_assoc, CompatibleIso.trans_symm, CompatibleIso.trans_refl]

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
