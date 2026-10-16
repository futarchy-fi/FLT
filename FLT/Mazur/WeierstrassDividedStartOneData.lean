/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedLowerData

/-!
# A depth-one extension of every positive finite divided family

The terminal datum supplies every earlier depth. The original family occurs
as the tail, with equality of actual coefficient data, not just residues.
The extended modification has extra stages; no equality of whole models is claimed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
variable {R : Type*} [CommRing R] {W : WeierstrassCurve R} {π : R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hstart : 0 < start)

/-- Number of transitions after extending the family back to depth one. -/
def startOneLength : ℕ := start + n - 1

/-- Every positive depth up to the original terminal depth, with integral coefficients. -/
def startOneData (i : Fin (startOneLength (start := start) (n := n) + 1)) :
    Data W π (1 + i.val) :=
  (data ⟨n, by omega⟩).lower (by
    change 1 + i.val ≤ start + n
    have := i.isLt
    have := hstart
    unfold startOneLength at *
    omega)

/-- The original depth index embedded as an index of the extended family. -/
def startOneTailIndex (i : Fin (n + 1)) :
    Fin (startOneLength (start := start) (n := n) + 1) :=
  ⟨start - 1 + i.val, by have := i.isLt; unfold startOneLength; omega⟩

/-- The embedded index represents exactly the original depth. -/
theorem startOneTailIndex_depth (i : Fin (n + 1)) :
    1 + (startOneTailIndex hstart i).val = start + i.val := by
  dsimp [startOneTailIndex]
  omega

include hstart in
/-- The final index of the extension is the original terminal depth. -/
theorem startOneLength_depth :
    1 + startOneLength (start := start) (n := n) = start + n := by
  unfold startOneLength
  omega

variable [IsDomain R] (hπ : π ≠ 0)

include hπ in
/-- Every original datum is recovered exactly on the tail of the extension. -/
theorem startOneData_tail (i : Fin (n + 1)) :
    (startOneData data hstart (startOneTailIndex hstart i)).lower
        (startOneTailIndex_depth hstart i).ge = data i :=
  Data.unique hπ _ _

include hπ in
/-- At any matching depth the extended datum is independent of the supplied family. -/
theorem startOneData_eq (i : Fin (startOneLength (start := start) (n := n) + 1))
    (d : Data W π (1 + i.val)) : startOneData data hstart i = d :=
  Data.unique hπ _ _

end FLT.Mazur.WeierstrassDividedDepth
