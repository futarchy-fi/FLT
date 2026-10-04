/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.IntegralQuotientFaithfullyFlat

/-!
# Fibres of the constructed integral quotient over integral points

The fibre is the actual tensor product along a point of the contracted quotient.
Its finite faithfully flat cover is derived from the quotient construction.
For a constant cyclic quotient the intended point is one, not the identity.
No Kummer parameter or identification with a multiplicative torsor is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K]
  [IsPrincipalIdealRing R] {X Q : FF R K}
  (q : GenericGaloisHom X Q) (f : q.quotientCoordinates →ₐ[R] R)

/-- The coordinate ring of the fibre over an actual integral quotient point. -/
def QuotientPointFiber :=
  let : Algebra q.quotientCoordinates R := f.toRingHom.toAlgebra
  R ⊗[q.quotientCoordinates] X.CoordinateRing

instance : CommRing (QuotientPointFiber (R := R) (K := K) q f) := by
  unfold QuotientPointFiber
  infer_instance

instance : Algebra R (QuotientPointFiber (R := R) (K := K) q f) := by
  unfold QuotientPointFiber
  infer_instance

instance : Module R (QuotientPointFiber (R := R) (K := K) q f) := Algebra.toModule

/-- The quotient fibre is finite over the original integral base. -/
instance quotientPointFiber_finite :
    Module.Finite R (QuotientPointFiber (R := R) (K := K) q f) := by
  let : Algebra q.quotientCoordinates R := f.toRingHom.toAlgebra
  let : Module.Finite q.quotientCoordinates X.CoordinateRing :=
    Module.Finite.of_restrictScalars_finite R q.quotientCoordinates X.CoordinateRing
  change Module.Finite R (R ⊗[q.quotientCoordinates] X.CoordinateRing)
  infer_instance

/-- Faithful flatness of the quotient supplies the faithfully flat fibre cover. -/
instance quotientPointFiber_faithfullyFlat :
    Module.FaithfullyFlat R (QuotientPointFiber (R := R) (K := K) q f) := by
  let : Algebra q.quotientCoordinates R := f.toRingHom.toAlgebra
  let := q.quotientCoordinatesFaithfullyFlat
  change Module.FaithfullyFlat R (R ⊗[q.quotientCoordinates] X.CoordinateRing)
  infer_instance

/-- A fibre over an integral point is nonempty as a faithfully flat scheme;
in particular its coordinate algebra is nontrivial when the base is. -/
instance quotientPointFiber_nontrivial :
    Nontrivial (QuotientPointFiber (R := R) (K := K) q f) :=
  (FaithfulSMul.algebraMap_injective R (QuotientPointFiber (R := R) (K := K) q f)).nontrivial

/-- The actual fibre coordinate algebra is finite flat over the base. -/
theorem quotientPointFiber_finite_flat :
    Module.Finite R (QuotientPointFiber (R := R) (K := K) q f) ∧
      Module.Flat R (QuotientPointFiber (R := R) (K := K) q f) := ⟨inferInstance, inferInstance⟩

end ThreeAdicPlan
