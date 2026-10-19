/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Assembly.Mazur

/-!
# The Frey-only input at prime exponents at least seventeen

The assembly needs irreducibility only for the curve of an actual Frey
package. Rational torsion bounds on arbitrary elliptic curves are a sufficient
producer of this input, not part of its statement.
-/

@[expose] public section

namespace FLT.Assembly

/-- The exact irreducibility input used by the large-prime Frey argument. -/
def FreyIrreducibility : Prop :=
  ∀ (P : FreyPackage), 17 ≤ P.p →
    have _instPrime : Fact P.p.Prime := ⟨P.pp⟩
    GaloisRep.IsIrreducible (P.freyCurve.galoisRep P.p P.hppos)

/-- The existing Mazur torsion exclusion supplies the narrower Frey-only input. -/
theorem freyIrreducibility_of_torsionExclusion
    (hmazur : MazurTorsionExclusion) : FreyIrreducibility := by
  intro P hp17
  exact P.mazur_of_torsionExclusion hmazur hp17

end FLT.Assembly
