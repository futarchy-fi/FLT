/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.ContinuousH1Comparison

/-!
# Continuous two-cocycles and actual continuous cohomology

Every homogeneous H² class has an explicit continuous representative, and
its vanishing is equivalent to the existence of a continuous one-cochain
whose differential is that representative.
-/

@[expose] public section

namespace GaloisRepresentation.Extensions

universe u

variable {k G M : Type u} [Field k] [TopologicalSpace k]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M] [ContinuousSMul k M]

/-- An explicit continuous two-cocycle in the homogeneous kernel. -/
def homogeneousTwoCocycle (c : C(G × G, M)) (hc : groupCohomology.IsCocycle₂ c) :
    HomogeneousKernel (k := k) (G := G) (M := M) 2 :=
  ⟨homogeneousTwo c, (homogeneousTwo_cocycle_iff c).mpr hc⟩

/-- The actual continuous cohomology class of an explicit continuous two-cocycle. -/
noncomputable def continuousH2Class (c : C(G × G, M)) (hc : groupCohomology.IsCocycle₂ c) :
    continuousCohomology 2 (TopRep.of (coefficientRepresentation k G M)) :=
  homogeneousClass 2 (homogeneousTwoCocycle c hc)

/-- The H² comparison reflects and preserves vanishing with a continuous witness. -/
theorem continuousH2Class_eq_zero (c : C(G × G, M)) (hc : groupCohomology.IsCocycle₂ c) :
    continuousH2Class (k := k) c hc = 0 ↔ ContinuousIsCoboundaryTwo c := by
  rw [continuousH2Class, homogeneousClass_eq_zero]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨inhomogeneousOne b, fun g h ↦ ?_⟩
    rw [← homogeneousOne_inhomogeneousOne b, ← homogeneousTwo_differential] at hb
    have he : continuousDifferentialOne (inhomogeneousOne b) = c := by
      simpa only [homogeneousTwoCocycle, inhomogeneousTwo_homogeneousTwo] using
        congrArg (fun f : (coefficientComplex k G M).X 2 ↦ inhomogeneousTwo f) hb
    exact congrArg (fun f : C(G × G, M) ↦ f (g, h)) he
  · rintro ⟨b, hb⟩
    refine ⟨homogeneousOne b, ?_⟩
    rw [← homogeneousTwo_differential]
    have he : continuousDifferentialOne b = c := by ext ⟨g, h⟩; exact hb g h
    exact congrArg (homogeneousTwo (k := k)) he

/-- Every continuous H² class has an explicit jointly continuous two-cocycle. -/
theorem continuousH2Class_surjective
    (x : continuousCohomology 2 (TopRep.of (coefficientRepresentation k G M))) :
    ∃ (c : C(G × G, M)) (hc : groupCohomology.IsCocycle₂ c), continuousH2Class c hc = x := by
  obtain ⟨z, rfl⟩ := homogeneousClass_surjective 2 x
  have hz : groupCohomology.IsCocycle₂ (inhomogeneousTwo z.1) :=
    (homogeneousTwo_cocycle_iff _).mp (by rw [homogeneousTwo_inhomogeneousTwo]; exact z.2)
  refine ⟨inhomogeneousTwo z.1, hz, ?_⟩
  change homogeneousClass 2 (homogeneousTwoCocycle _ hz) = homogeneousClass 2 z
  apply congrArg (homogeneousClass 2)
  exact Subtype.ext (homogeneousTwo_inhomogeneousTwo z.1)

end GaloisRepresentation.Extensions
