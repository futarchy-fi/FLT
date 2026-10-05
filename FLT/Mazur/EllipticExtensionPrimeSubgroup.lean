/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The prime-order subgroup in an extended elliptic model

Base change and an actual generic variable change embed the original point
group into the new model. A nonzero p-torsion point generates a subgroup
of order p there. This constructs the generic subgroup, not its integral closure.
-/

@[expose] public noncomputable section

namespace FLT.Mazur

open WeierstrassCurve

variable {R S K L : Type*} [CommRing R] [CommRing S] [Field K] [Field L]
  [Algebra R K] [Algebra R L] [Algebra K L] [IsScalarTower R K L] [Algebra S L]
  [DecidableEq K] [DecidableEq L]
  (W : WeierstrassCurve R) (U : WeierstrassCurve S)
  [(W.map (algebraMap R L)).IsElliptic] (C : VariableChange L)
  (hC : C • W.map (algebraMap R L) = U.map (algebraMap S L))

/-- Transport actual rational points to the generic fiber of the extended model. -/
def ellipticExtensionPointHom :
    (W.map (algebraMap R K)).toAffine.Point →+
      (U.map (algebraMap S L)).toAffine.Point :=
  (Affine.Point.equivOfEq hC).toAddMonoidHom.comp
    ((Affine.Point.equivVariableChange (W.map (algebraMap R L)) C).symm.toAddMonoidHom.comp
      (Affine.Point.map (IsScalarTower.toAlgHom R K L)))

/-- Neither the field extension nor the variable change collapses distinct points. -/
theorem ellipticExtensionPointHom_injective :
    Function.Injective (ellipticExtensionPointHom (K := K) W U C hC) :=
  (Affine.Point.equivOfEq hC).injective.comp
    ((Affine.Point.equivVariableChange (W.map (algebraMap R L)) C).symm.injective.comp
      (Affine.Point.map_injective (W' := W.toAffine) (IsScalarTower.toAlgHom R K L)))

/-- The transported generator still has exact order p. -/
theorem ellipticExtensionPoint_addOrderOf {p : ℕ} [Fact p.Prime]
    (P : (W.map (algebraMap R K)).toAffine.Point) (hP : p • P = 0) (hP0 : P ≠ 0) :
    addOrderOf (ellipticExtensionPointHom W U C hC P) = p := by
  rw [addOrderOf_injective _ (ellipticExtensionPointHom_injective W U C hC)]
  exact addOrderOf_eq_prime hP hP0

/-- The actual cyclic subgroup on the new generic fiber has p elements. -/
theorem ellipticExtensionPrimeSubgroup_card {p : ℕ} [Fact p.Prime]
    (P : (W.map (algebraMap R K)).toAffine.Point) (hP : p • P = 0) (hP0 : P ≠ 0) :
    Nat.card (AddSubgroup.zmultiples (ellipticExtensionPointHom W U C hC P)) = p := by
  rw [Nat.card_zmultiples, ellipticExtensionPoint_addOrderOf W U C hC P hP hP0]

end FLT.Mazur
