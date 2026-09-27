/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.WeilPairing
public import FLT.Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# The determinant of elliptic-curve torsion from the Weil pairing

All results in this file take a checked Weil pairing as input. Constructing that
pairing remains a separate obligation.
-/

@[expose] public section

namespace WeierstrassCurve.TorsionWeilPairing

variable {K : Type*} [Field K] {E : WeierstrassCurve K} [E.IsElliptic]
  [DecidableEq (AlgebraicClosure K)] {p : ℕ} [Fact p.Prime]

/-- A checked Weil pairing identifies the determinant on prime torsion with the
modular cyclotomic character. -/
theorem det_torsionGaloisRepresentation (w : E.TorsionWeilPairing p)
    [NeZero (p : K)] (g : Field.absoluteGaloisGroup K) :
    (E.torsionGaloisRepresentation p g).det =
      modularCyclotomicCharacter (AlgebraicClosure K)
        (HasEnoughRootsOfUnity.natCard_rootsOfUnity _ p) g.toRingEquiv := by
  let : NeZero (p : AlgebraicClosure K) :=
    ‹NeZero (p : K)›.of_injective (algebraMap K (AlgebraicClosure K)).injective
  have hd := (E.map (algebraMap K (AlgebraicClosure K))).finrank_prime_torsion p
    (NeZero.ne _)
  let := Module.nontrivial_of_finrank_eq_succ hd
  let b := Module.finBasisOfFinrankEq (ZMod p)
    ((E.map (algebraMap K (AlgebraicClosure K))).nTorsion p) hd
  exact w.pairing.det_eq_of_similitude b w.pairing_ne_zero _ _
    (w.map_eq_cyclotomic_smul _ g)

/-- The continuous torsion representation has the reduction of the p-adic cyclotomic
character as determinant, provided a checked Weil pairing is supplied. -/
theorem det_galoisRep (w : E.TorsionWeilPairing p) [DecidableEq K] [NeZero (p : K)]
    (hp : 0 < p) (g : Field.absoluteGaloisGroup K) :
    (E.galoisRep p hp).det g =
      PadicInt.toZMod (cyclotomicCharacter (AlgebraicClosure K) p g.toRingEquiv).val := by
  change (E.torsionGaloisRepresentation p g).det = _
  rw [cyclotomicCharacter.toZMod (HasEnoughRootsOfUnity.natCard_rootsOfUnity _ p)]
  exact w.det_torsionGaloisRepresentation g

end WeierstrassCurve.TorsionWeilPairing
