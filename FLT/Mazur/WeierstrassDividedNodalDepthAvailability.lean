/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthAvailability
public import FLT.Mazur.WeierstrassNodalDividedDepth
public import FLT.Mazur.EllipticNodeComponentLabel

/-!
# Actual finite depth data from split-node coefficients

At node depth four times the input depth, the terminal datum at twice the
input depth exists. It supplies the whole finite family. The terminal fourth
quotient has zero residue and the constant quotient is a unit, as required
by the horizontal smoothness criterion.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open IsLocalRing
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {k : ℕ} (D : SplitNodeDepth W π (4 * k))

/-- The original split-node depth constructs the available doubled-depth datum. -/
def splitNodeDoubledData : Data W π (k + k) :=
  (nodalDepth_exists_data D.maximalIdeal_eq (by omega : 2 * (k + k) ≤ 4 * k)
    D.a₃_mem D.a₄_mem D.a₆_mem).some

/-- Every required intermediate datum is constructed from the original coefficients. -/
def splitNodeDoubledFamily (i : Fin (k + k + 1)) : Data W π (0 + i.val) :=
  (splitNodeDoubledData D).truncate (by have h := i.isLt; omega)

include D in
/-- The actual terminal fourth quotient vanishes in the base residue ring. -/
theorem splitNodeDoubledData_fourth_mem (e : Data W π (k + k)) :
    e.b4 ∈ maximalIdeal R :=
  (nodalDepth_linear_mem D.uniformizer_ne_zero D.maximalIdeal_eq e
    (by omega : 2 * (k + k) ≤ 4 * k) D.a₃_mem D.a₄_mem).2

omit [IsDomain R] in
include D in
/-- The terminal constant quotient is a unit by the exact original node depth. -/
theorem splitNodeDoubledData_constant_unit (e : Data W π (k + k)) : IsUnit e.b6 :=
  nodalDepth_constant_isUnit D.maximalIdeal_eq e (by omega) D.a₆_not_mem

/-- The constructed family recovers any chosen datum at the same available depth. -/
theorem splitNodeDoubledFamily_agrees (i : Fin (k + k + 1))
    (d : Data W π (0 + i.val)) : splitNodeDoubledFamily D i = d :=
  Data.eq_of_depth D.uniformizer_ne_zero _ _

end FLT.Mazur.WeierstrassDividedDepth
