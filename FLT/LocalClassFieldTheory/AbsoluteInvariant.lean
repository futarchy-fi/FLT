/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedInflationSurjective

/-!
# The absolute local invariant

Invert the proved bijective unramified inflation, then use normalized order
and arithmetic Frobenius on the unramified union. This constructs the actual
additive isomorphism from absolute multiplicative H² to Q/Z.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory

variable (R K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C] [CharZero C]
  [IsAdicComplete (maximalIdeal R) R]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]

attribute [local instance] unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete
  relativeBaseTower

/-- The proved unramified inflation as an additive equivalence. -/
def absoluteInflationEquiv :
    continuousCohomology ℤ Gal(maximalUnramified R K C/K)
      (Additive (maximalUnramified R K C)ˣ) 2 ≃+
    continuousCohomology ℤ Gal(C/K) (Additive Cˣ) 2 :=
  (LinearEquiv.ofBijective (unramifiedMultiplicativeInflation R K C 2).hom
    (unramifiedMultiplicativeInflationH2_bijective R K C p)).toAddEquiv

/-- The absolute local invariant, normalized by arithmetic Frobenius and integer order. -/
def absoluteInvariant : continuousCohomology ℤ Gal(C/K) (Additive Cˣ) 2 ≃+
    AddCircle (1 : ℚ) :=
  (absoluteInflationEquiv R K C p).symm.trans (unramifiedMultiplicativeInvariant R K C)

/-- The absolute invariant extends the already normalized unramified invariant. -/
theorem absoluteInvariant_inflation
    (x : continuousCohomology ℤ Gal(maximalUnramified R K C/K)
      (Additive (maximalUnramified R K C)ˣ) 2) :
    absoluteInvariant R K C p ((unramifiedMultiplicativeInflation R K C 2).hom x) =
      unramifiedMultiplicativeInvariant R K C x := by
  change unramifiedMultiplicativeInvariant R K C
    ((absoluteInflationEquiv R K C p).symm ((absoluteInflationEquiv R K C p) x)) = _
  rw [AddEquiv.symm_apply_apply]

/-- The class with a prescribed invariant is the inflation of its unramified representative. -/
theorem absoluteInvariant_symm_apply (x : AddCircle (1 : ℚ)) :
    (absoluteInvariant R K C p).symm x =
      (unramifiedMultiplicativeInflation R K C 2).hom
        ((unramifiedMultiplicativeInvariant R K C).symm x) := rfl

end LocalClassFieldTheory
