/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LocalConstantIdentification
public import FLT.GroupScheme.OrdinaryIntegralQuotientPoint

/-!
# The actual ordinary integral quotient is constant

For a trivial quotient character over a small-ramification local base, the
contracted quotient is identified with the explicit constant model. This works
for finite coefficient fields of any degree and derives integral étaleness.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open NumberField IsLocalRing GaloisRepresentation.Extensions
namespace ThreeAdicPlan

variable {K k : Type} [Field K] [NumberField K] [Field k] [Finite k]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  [IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K)]
  (p : ℕ) [Fact p.Prime] [CharP k p]
  [CharP (ResidueField (v.adicCompletionIntegers K)) p]
  (X : FF (v.adicCompletionIntegers K) (v.adicCompletion K)) [Module k X.Points]
  [SMulCommClass (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
    AlgebraicClosure (v.adicCompletion K)) k X.Points]
  {α β : (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
    AlgebraicClosure (v.adicCompletion K)) →* kˣ}
  (E : OrdinaryFiltration (Representation.ofDistribMulAction k
    (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
      AlgebraicClosure (v.adicCompletion K)) X.Points) α β)
  (he : RaynaudParameters.order (p : v.adicCompletionIntegers K) < p - 1) (hβ : β = 1)

local instance : IsDedekindDomain (v.adicCompletionIntegers K) :=
  IsPrincipalIdealRing.isDedekindDomain _

/-- The contracted quotient has the explicit constant integral Hopf algebra. -/
def ordinaryLocalConstantIso : (ordinaryQuotientModel X E).Iso
    (constantGroupModel (v.adicCompletionIntegers K) (v.adicCompletion K) k) := by
  apply (existsUnique_local_constant_iso v p (ordinaryQuotientModel X E) he ?_ ?_).choose
  · intro x
    change p • (show k from x) = 0
    rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  · intro g x
    change (β g : k) * (show k from x) = (show k from x)
    simp [hβ]

/-- The integral isomorphism induces the prescribed identity on quotient vectors. -/
theorem ordinaryLocalConstantIso_point (x : k) :
    genericHom (ordinaryLocalConstantIso v p X E he hβ).toBialgHom x =
      constantGroupPoint (v.adicCompletionIntegers K) (v.adicCompletion K) k x := by
  exact (existsUnique_local_constant_iso v p (ordinaryQuotientModel X E) he
    (fun x ↦ by
      change p • (show k from x) = 0
      rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul])
    (fun g x ↦ by
      change (β g : k) * (show k from x) = (show k from x)
      simp [hβ])).choose_spec.1 x

/-- The previously constructed quotient point is evaluation at one in the constant model. -/
theorem ordinaryLocalConstantIso_one
    (a : (constantGroupModel (v.adicCompletionIntegers K) (v.adicCompletion K) k).CoordinateRing) :
    ordinaryIntegralQuotientPoint X E hβ (ordinaryLocalConstantIso v p X E he hβ a) =
      constantGroupIntegralPoint (v.adicCompletionIntegers K) (v.adicCompletion K) k 1 a := by
  have h := integralPoints_genericHom
    (X := ordinaryQuotientModel X E)
    (Y := constantGroupModel (v.adicCompletionIntegers K) (v.adicCompletion K) k)
    (ordinaryLocalConstantIso v p X E he hβ).toBialgHom (1 : k)
  rw [ordinaryLocalConstantIso_point, constantGroupPoint_integral] at h
  apply (algebraMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))).injective.comp
    (IsFractionRing.injective (v.adicCompletionIntegers K) (v.adicCompletion K))
  have hp := AlgHom.congr_fun (ordinaryIntegralQuotientPoint_spec X E hβ)
    (ordinaryLocalConstantIso v p X E he hβ a)
  exact hp.trans (AlgHom.congr_fun h a).symm

/-- The specified quotient coordinates are the integral function algebra. -/
def ordinaryLocalConstantCoordinates :
    (ordinaryQuotientModel X E).CoordinateRing ≃ₐ[v.adicCompletionIntegers K]
      (Multiplicative k → v.adicCompletionIntegers K) :=
  (ordinaryLocalConstantIso v p X E he hβ).symm.toAlgEquiv.trans
    (constantGroupCoordinates _ _ k)

include he hβ in
/-- Integral étaleness of the actual quotient follows from the constructed isomorphism. -/
theorem ordinaryLocalQuotient_etale :
    Algebra.Etale (v.adicCompletionIntegers K) (ordinaryQuotientModel X E).CoordinateRing :=
  Algebra.Etale.of_equiv (ordinaryLocalConstantCoordinates v p X E he hβ).symm

end ThreeAdicPlan
