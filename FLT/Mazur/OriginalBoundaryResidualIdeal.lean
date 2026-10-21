/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryLiftFiniteSupport
public import Mathlib.RingTheory.Finiteness.Ideal

/-!
# The original residual boundary ideal and uniform lift powers

The sum of the exact boundary kernel and the finite-locus avoidance ideal
cuts out precisely the intersection of the two image closures. Its radical
is contained in the radical of every original boundary lift ideal. A finitely
generated original ideal supported there therefore has one power giving
exact full-source lifts; no Noetherianity of the invariant ring is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open SchemeEffectiveEpiSections SchemeOpenEnvelope SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A S : Scheme.{0}} {p q : D ⟶ A} (J : A.IdealSheafData)
local notation "σ" => Subring.subtype (compatibleFunctions p q)

/-- Original scalars detecting the residual boundary/nonfinite intersection. -/
def originalBoundaryResidualIdeal : Ideal (compatibleFunctions p q) :=
  originalBoundaryScalarKernel J ⊔ scalarAvoidanceIdeal σ (finiteTargetOpen p)

variable [IsAffine A]

/-- The sum keeps both closures separately, with no image/intersection interchange. -/
theorem originalBoundaryResidualIdeal_zeroLocus :
    PrimeSpectrum.zeroLocus
        (originalBoundaryResidualIdeal (p := p) (q := q) J : Set (compatibleFunctions p q)) =
      closure (scalarMorphism σ '' (J.support : Set A)) ∩
        closure (scalarMorphism σ '' (finiteTargetOpen p : Set A)ᶜ) := by
  rw [originalBoundaryResidualIdeal, PrimeSpectrum.zeroLocus_sup,
    originalBoundaryScalarKernel_zeroLocus, scalarAvoidanceIdeal,
    PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]

variable [IsSeparated p] [Etale p] [QuasiCompact p]
  (e : CategoryTheory.EquivalenceRelation p q) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  (t : compatibleFunctions (pullback.snd p J.subschemeι)
    (InvariantIdealRelation.snd J p q hJ))

include e hf in
/-- The geometric residual ideal gives full original lifts after scalar powers. -/
theorem originalBoundaryResidualIdeal_le_lift_radical :
    originalBoundaryResidualIdeal (p := p) (q := q) J ≤
      (originalBoundaryLiftIdeal (p := p) (q := q) J t.val).radical := by
  exact sup_le ((originalBoundaryScalarKernel_le_liftIdeal J t.val).trans Ideal.le_radical)
    (finiteAvoidanceIdeal_le_originalBoundaryLiftIdeal_radical e J hJ f hf t)

include e hf in
/-- Testing only the residual intersection gives one power of a finitely generated scalar ideal. -/
theorem exists_pow_le_originalBoundaryLiftIdeal_of_residual
    (Q : Ideal (compatibleFunctions p q)) (hfg : Q.FG)
    (hQ : closure (scalarMorphism σ '' (J.support : Set A)) ∩
        closure (scalarMorphism σ '' (finiteTargetOpen p : Set A)ᶜ) ⊆
      PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q))) :
    ∃ N : ℕ, Q ^ N ≤ originalBoundaryLiftIdeal (p := p) (q := q) J t.val := by
  exact Ideal.exists_pow_le_of_le_radical_of_fg
    ((PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp
      ((originalBoundaryLift_support_subset_boundary_nonfinite e J hJ f hf t).trans hQ)) hfg

include e hf in
/-- Disjoint bad-image closures construct an unscaled original invariant boundary lift. -/
theorem exists_originalBoundaryLift_of_disjoint_images
    (h : Disjoint (closure (scalarMorphism σ '' (J.support : Set A)))
      (closure (scalarMorphism σ '' (finiteTargetOpen p : Set A)ᶜ))) :
    ∃ r : compatibleFunctions p q, J.subschemeι.appTop r.val = t.val := by
  apply (one_mem_originalBoundaryLiftIdeal J t.val).mp
  have hz := originalBoundaryLift_support_subset_boundary_nonfinite e J hJ f hf t
  rw [Set.disjoint_iff_inter_eq_empty.mp h] at hz
  have ht := PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp (Set.eq_empty_of_subset_empty hz)
  rw [ht]
  trivial

end FLT.Mazur.EquivalenceRelationOrderedFrames
