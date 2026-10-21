/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageFiniteLocusCorrection
public import FLT.Mazur.SchemeScalarAvoidanceIdeal

/-!
# Original boundary lifting away from the residual intersection

Finite original neighborhoods give powers in the original lift ideal itself.
Together with the exact boundary kernel this controls original-source lifting
failure by the intersection of two image closures, before choosing any rank.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open SchemeEffectiveEpiSections SchemeOpenEnvelope SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A S : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [IsAffine A] (e : CategoryTheory.EquivalenceRelation p q)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  (t : compatibleFunctions (pullback.snd p J.subschemeι)
    (InvariantIdealRelation.snd J p q hJ))
local notation "σ" => Subring.subtype (compatibleFunctions p q)

include e hf in
/-- Finite original principal neighborhoods provide exact full-source lift denominators. -/
theorem exists_pow_mem_originalBoundaryLiftIdeal_of_finite
    (r : compatibleFunctions p q) (hr : A.basicOpen r.val ≤ finiteTargetOpen p) :
    ∃ N : ℕ, r ^ N ∈ originalBoundaryLiftIdeal (p := p) (q := q) J t.val := by
  let _ : IsFinite (p.resLE (A.basicOpen r.val) _ le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact finite_restrict_of_le_finiteTarget p _ hr
  obtain ⟨u, hu⟩ := InvariantAffineFiniteBoundaryLift.exists_lift p q e
    (A.basicOpen r.val) (compatibleFunctions_basicOpen p q r)
    (compatibleFunctions_basicOpen_affine p q r) J hJ f hf t
  let _ := QuasiCompact.compactSpace_of_compactSpace p
  let _ := quasiSeparatedSpace_of_quasiSeparated p
  exact exists_pow_mem_originalBoundaryLiftIdeal J t.val r u hu

include e hf in
/-- Every finite-locus avoidance scalar is radical in the exact original lift ideal. -/
theorem finiteAvoidanceIdeal_le_originalBoundaryLiftIdeal_radical :
    scalarAvoidanceIdeal σ (finiteTargetOpen p) ≤
      (originalBoundaryLiftIdeal (p := p) (q := q) J t.val).radical := by
  intro r hr
  exact exists_pow_mem_originalBoundaryLiftIdeal_of_finite e J hJ f hf t r
    ((mem_scalarAvoidanceIdeal_iff σ (finiteTargetOpen p) r).mp hr)

include e hf in
/-- Original full-source lifting failure is confined to both closed bad images. -/
theorem originalBoundaryLift_support_subset_boundary_nonfinite :
    PrimeSpectrum.zeroLocus
        (originalBoundaryLiftIdeal (p := p) (q := q) J t.val :
          Set (compatibleFunctions p q)) ⊆
      closure (scalarMorphism σ '' (J.support : Set A)) ∩
        closure (scalarMorphism σ '' (finiteTargetOpen p : Set A)ᶜ) := by
  intro x hx
  constructor
  · rw [← originalBoundaryScalarKernel_zeroLocus]
    exact (originalBoundaryScalarKernel_le_liftIdeal J t.val).trans hx
  · rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    change scalarAvoidanceIdeal σ (finiteTargetOpen p) ≤ x.asIdeal
    exact (finiteAvoidanceIdeal_le_originalBoundaryLiftIdeal_radical e J hJ f hf t).trans
      (x.isPrime.radical_le_iff.mpr hx)

end FLT.Mazur.EquivalenceRelationOrderedFrames
