/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Norm.Quotient
public import Mathlib.RingTheory.Trace.Quotient
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Norm and trace on the residue extension

For a finite free unramified local algebra, the maximal ideal is the extended
base maximal ideal. Thus the quotient norm and trace formulas compute the
norm and trace of the actual residue extension.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing

variable (R S : Type*) [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)]
  [Module.Finite R S] [Module.Free R S] [Algebra.FormallyUnramified R S]

/-- The base-ideal quotient agrees with the actual residue field in an
unramified local algebra, over the base residue field. -/
def unramifiedResidueQuotientEquiv :
    (S ⧸ (maximalIdeal R).map (algebraMap R S)) ≃ₐ[R ⧸ maximalIdeal R] (S ⧸ maximalIdeal S) :=
  let e : (S ⧸ (maximalIdeal R).map (algebraMap R S)) ≃ₐ[R] (S ⧸ maximalIdeal S) :=
    Ideal.quotientEquivAlgOfEq R
      (Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := S))
  e.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := maximalIdeal R))

omit [Module.Free R S] in
/-- The quotient equivalence preserves the class of each integral element. -/
@[simp] theorem unramifiedResidueQuotientEquiv_mk (x : S) :
    unramifiedResidueQuotientEquiv R S (Ideal.Quotient.mk _ x) = residue S x := rfl

/-- Norm commutes with reduction in an unramified local algebra. -/
theorem residue_norm (x : S) :
    residue R (Algebra.norm R x) =
      Algebra.norm (ResidueField R) (residue S x) := by
  change Ideal.Quotient.mk (maximalIdeal R) (Algebra.norm R x) = _
  rw [← norm_quotient_mk, ← unramifiedResidueQuotientEquiv_mk R S x]
  exact (Algebra.norm_eq_of_algEquiv (unramifiedResidueQuotientEquiv R S) _).symm

/-- Trace commutes with reduction in an unramified local algebra. -/
theorem residue_trace (x : S) :
    residue R (Algebra.trace R S x) =
      Algebra.trace (ResidueField R) (ResidueField S) (residue S x) := by
  change Ideal.Quotient.mk (maximalIdeal R) (Algebra.trace R S x) = _
  rw [← Algebra.trace_quotient_mk, ← unramifiedResidueQuotientEquiv_mk R S x]
  exact (Algebra.trace_eq_of_algEquiv (unramifiedResidueQuotientEquiv R S) _).symm

end LocalClassFieldTheory
