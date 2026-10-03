/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.HomogeneousTwo

/-!
# Continuous degree-one classes and homogeneous cohomology

The comparison uses the actual kernel/cokernel model of continuous cohomology.
Principals are proved to correspond to boundaries, not supplied as input.
-/

@[expose] public section

namespace GaloisRepresentation.Extensions

universe u

open CategoryTheory ContinuousCohomology

variable {k G M : Type u} [Field k] [TopologicalSpace k]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M] [ContinuousSMul k M]

/-- The homogeneous kernel model in any degree. -/
abbrev HomogeneousKernel (n : ℕ) :=
  TopModuleCat.ker ((coefficientComplex k G M).d n (n + 1))

/-- Send a kernel representative to actual continuous cohomology. -/
noncomputable def homogeneousClass (n : ℕ) :
    HomogeneousKernel (k := k) (G := G) (M := M) n →ₗ[k]
      continuousCohomology n (TopRep.of (coefficientRepresentation k G M)) :=
  (cohomologyIsoQuot _ n).inv.hom.toLinearMap.comp
    (TopModuleCat.cokerπ (bdryKer _ n)).hom.toLinearMap

/-- Zero in continuous cohomology means an actual homogeneous boundary. -/
theorem homogeneousClass_eq_zero (n : ℕ)
    (c : HomogeneousKernel (k := k) (G := G) (M := M) n) :
    homogeneousClass n c = 0 ↔
      ∃ b : (coefficientComplex k G M).X (n - 1),
        (coefficientComplex k G M).d (n - 1) n b = c.1 := by
  have hi := ConcreteCategory.bijective_of_isIso (cohomologyIsoQuot
    (TopRep.of (coefficientRepresentation k G M)) n).inv
  change (cohomologyIsoQuot _ n).inv (TopModuleCat.cokerπ (bdryKer _ n) c) = 0 ↔ _
  rw [← map_zero (cohomologyIsoQuot
    (TopRep.of (coefficientRepresentation k G M)) n).inv.hom, hi.1.eq_iff,
    TopModuleCat.cokerπ_eq_zero_iff]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, congrArg Subtype.val hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, Subtype.ext hb⟩

/-- Every continuous cohomology class has a homogeneous kernel representative. -/
theorem homogeneousClass_surjective (n : ℕ) :
    Function.Surjective (homogeneousClass (k := k) (G := G) (M := M) n) := by
  intro x
  obtain ⟨c, hc⟩ := TopModuleCat.cokerπ_surjective (bdryKer
    (TopRep.of (coefficientRepresentation k G M)) n) ((cohomologyIsoQuot _ n).hom x)
  refine ⟨c, ?_⟩
  change (cohomologyIsoQuot _ n).inv (TopModuleCat.cokerπ (bdryKer _ n) c) = x
  rw [hc]
  exact congr($(Iso.hom_inv_id (cohomologyIsoQuot _ n)) x)

/-- The one-cocycle equation is exactly the homogeneous kernel condition. -/
theorem homogeneousOne_cocycle_iff (c : C(G, M)) :
    (coefficientComplex k G M).d 1 2 (homogeneousOne c) = 0 ↔
      groupCohomology.IsCocycle₁ c := by
  constructor
  · intro hc g h
    have he := congrArg (fun f : (coefficientComplex k G M).X 2 ↦ f.1 1 g (g * h)) hc
    rw [homogeneous_d_one] at he
    simp only [inv_mul_cancel_left, inv_one, one_mul, one_smul] at he
    change c (g * h) = g • c h + c g
    apply sub_eq_zero.mp
    calc
      _ = -(g • c h - c (g * h) + c g) := by abel
      _ = 0 := by rw [he]; simp
  · intro hc
    apply Subtype.ext
    ext g h j
    rw [homogeneous_d_one]
    have he := congrArg (fun m : M ↦ g • m) (hc (g⁻¹ * h) (h⁻¹ * j))
    simp only [mul_assoc, mul_inv_cancel_left, smul_add, smul_smul] at he
    change _ = 0
    rw [he]
    abel

/-- An explicit continuous cocycle as a homogeneous kernel representative. -/
def homogeneousOneCocycle (c : ContinuousCocycle G M) :
    HomogeneousKernel (k := k) (G := G) (M := M) 1 :=
  ⟨homogeneousOne c.1, (homogeneousOne_cocycle_iff c.1).mpr c.2⟩

/-- The continuous cohomology class of an explicit one-cocycle. -/
noncomputable def continuousH1Class (c : ContinuousCocycle G M) :
    continuousCohomology 1 (TopRep.of (coefficientRepresentation k G M)) :=
  homogeneousClass 1 (homogeneousOneCocycle c)

/-- Vanishing of the comparison is exactly principality with a coefficient witness. -/
theorem continuousH1Class_eq_zero (c : ContinuousCocycle G M) :
    continuousH1Class (k := k) c = 0 ↔ ∃ a : M, ∀ g, c.1 g = g • a - a := by
  rw [continuousH1Class, homogeneousClass_eq_zero]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b.1 1, fun g ↦ ?_⟩
    change (coefficientComplex k G M).d 0 1 b = homogeneousOne c.1 at hb
    rw [← homogeneousZero_eval b] at hb
    have he := congrArg (fun f : (coefficientComplex k G M).X 1 ↦ f.1 1 g) hb
    rw [homogeneous_d_zero] at he
    simpa [homogeneousOne] using he.symm
  · rintro ⟨a, ha⟩
    refine ⟨homogeneousZero a, ?_⟩
    apply Subtype.ext
    ext g h
    rw [homogeneous_d_zero]
    change h • a - g • a = g • c.1 (g⁻¹ * h)
    rw [ha, smul_sub, smul_smul, mul_inv_cancel_left]

end GaloisRepresentation.Extensions
