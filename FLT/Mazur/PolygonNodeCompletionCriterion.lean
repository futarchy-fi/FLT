/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveNodeAffineCompletion
public import FLT.Mazur.NodeSmoothLocus
/-!
# Exact completion criteria for the polygon node charts

The unique nonsmooth point is the maximal kernel of evaluation.
The completed affine ring criterion is equivalent to AtWorstNodes for
each chart. The two power-series algebra isomorphisms remain to be proved.
-/

open CategoryTheory AlgebraicGeometry
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace FLT.Mazur.PolygonNodeCompletionCriterion
open FCurve.CurveNode
section general
variable (K A : Type u) [Field K] [CommRing A] [Algebra K A]
  (e : A →ₐ[K] K)
  [LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap K A)))]
theorem affine (hs : ((Spec.map (CommRingCat.ofHom (algebraMap K A))).smoothLocus :
    Set (Spec (.of A))) = (PrimeSpectrum.zeroLocus (RingHom.ker e.toRingHom))ᶜ) :
    AtWorstNodes (Spec.map (CommRingCat.ofHom (algebraMap K A))) ↔
      Nonempty (AdicCompletion (RingHom.ker e.toRingHom) A ≃ₐ[K] Model K) := by
  have hm := RingHom.ker_isMaximal_of_surjective e.toRingHom
    (fun a ↦ ⟨algebraMap K A a, e.commutes a⟩)
  let p : PrimeSpectrum A := ⟨RingHom.ker e.toRingHom, inferInstance⟩
  have hp : p.asIdeal.IsMaximal := hm
  have hz : PrimeSpectrum.zeroLocus (RingHom.ker e.toRingHom) = {p} := by
    ext y
    constructor
    · intro hy
      exact PrimeSpectrum.ext (hm.eq_of_le y.isPrime.ne_top hy).symm
    · rintro rfl
      change RingHom.ker e.toRingHom ≤ p.asIdeal
      exact le_rfl
  have hc : IsClosed ({p} : Set (Spec (.of A))) := by
    rw [← hz]
    exact PrimeSpectrum.isClosed_zeroLocus _
  rw [← CurveNodeAffineCompletion.isNode_iff K A p]
  constructor
  · intro h
    rcases h p hc with hsm | hnode
    · change p ∈ ((Spec.map (CommRingCat.ofHom (algebraMap K A))).smoothLocus :
        Set (Spec (.of A))) at hsm
      rw [hs, hz] at hsm
      exact (hsm (Set.mem_singleton p)).elim
    · exact hnode
  · intro hp y _
    by_cases hy : y = p
    · subst y
      exact Or.inr hp
    · left
      change y ∈ ((Spec.map (CommRingCat.ofHom (algebraMap K A))).smoothLocus : Set (Spec (.of A)))
      rw [hs, hz]
      exact hy
end general
open PolygonNodePresentation PolygonNodeEqualizer
variable (K : Type u) [Field K]
theorem split_node : AtWorstNodes (aToBase K) ↔
    Nonempty (AdicCompletion (RingHom.ker (aEval (R := K)).toRingHom) (A (R := K)) ≃ₐ[K]
      Model K) := by
  apply affine K _ aEval
  exact (a_smooth_complement K).trans (congrArg Set.compl (range_aOrigin K))
theorem one_gon : AtWorstNodes (bToBase K) ↔
    Nonempty (AdicCompletion (RingHom.ker (bEval (R := K)).toRingHom) (B (R := K)) ≃ₐ[K]
      Model K) := by
  apply affine K _ bEval
  exact (b_smooth_complement K).trans (congrArg Set.compl (range_bOrigin K))
end FLT.Mazur.PolygonNodeCompletionCriterion
