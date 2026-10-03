/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.HomogeneousCup
public import FLT.GaloisRepresentation.Extensions.ContinuousH1Equiv

/-!
# Comparison with the cup product on continuous cohomology

The explicit cup represents the existing homogeneous cup on actual H¹ and H².
No local invariant or arithmetic duality statement is assumed here.
-/

@[expose] public section

namespace GaloisRepresentation.Extensions

universe u

open CategoryTheory ContinuousCohomology ContinuousLinearMap.CompactOpen

variable {k G M : Type u} [Field k] [TopologicalSpace k] [DiscreteTopology k]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M] [ContinuousSMul k M]

/-- The actual continuous cohomology cup with a trivial character. -/
noncomputable def continuousCohomologyCup
    (x : continuousCohomology 1 (TopRep.of (coefficientRepresentation k G M)))
    (d : ContinuousAddCharacter G k) :
    continuousCohomology 2 (TopRep.of (coefficientRepresentation k G M)) :=
  cup (coefficientRepresentation k G M) (ContRepresentation.trivial k G k)
    (coefficientRepresentation k G M) scalarCupPairing scalarCupPairing_continuous
    1 1 2 rfl x (trivialH1Class d)

/-- Passing through the quotient models preserves the explicit cup formula. -/
theorem continuousCohomologyCup_class (c : ContinuousCocycle G M)
    (d : ContinuousAddCharacter G k) :
    continuousCohomologyCup (continuousH1Class c) d =
      continuousH2Class (continuousCup c d) (continuousCup_isCocycle c d) := by
  let A := TopRep.of (coefficientRepresentation k G M)
  let B := TopRep.of (ContRepresentation.trivial k G k)
  let z := homogeneousOneCocycle (k := k) c
  let w := trivialOneCocycle d
  change (cohomologyIsoQuot A 2).inv
    (TopModuleCat.cokerDescBilinear (bdryKer A 1) (bdryKer B 1) (bdryKer A 2)
      (cupKerHom scalarCupPairing scalarCupPairing_continuous 1 1 2 rfl)
      _ _ _
      ((cohomologyIsoQuot A 1).hom
        ((cohomologyIsoQuot A 1).inv (TopModuleCat.cokerπ (bdryKer A 1) z)))
      ((cohomologyIsoQuot B 1).hom
        ((cohomologyIsoQuot B 1).inv (TopModuleCat.cokerπ (bdryKer B 1) w)))) = _
  rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
  change homogeneousClass 2
    (cupKerCLM scalarCupPairing scalarCupPairing_continuous 1 1 2 rfl z w) = _
  apply congrArg (homogeneousClass 2)
  apply Subtype.ext
  exact homogeneousCup_eq c d

/-- On the original splitting quotient the cup comparison has the same formula. -/
theorem continuousCohomologyCup_mk (c : ContinuousCocycle G M)
    (d : ContinuousAddCharacter G k) :
    continuousCohomologyCup (continuousH1Equiv (k := k) (continuousClassMk c)) d =
      continuousH2Class (continuousCup c d) (continuousCup_isCocycle c d) := by
  rw [continuousH1Equiv_mk, continuousCohomologyCup_class]

variable [LocallyCompactSpace G]

/-- Actual continuous-cohomology cup vanishing is the explicit continuous coboundary condition. -/
theorem continuousCohomologyCup_eq_zero (c : ContinuousCocycle G M)
    (d : ContinuousAddCharacter G k) :
    continuousCohomologyCup (continuousH1Class c) d = 0 ↔
      ContinuousIsCoboundaryTwo (continuousCup c d) := by
  rw [continuousCohomologyCup_class, continuousH2Class_eq_zero]

end GaloisRepresentation.Extensions
