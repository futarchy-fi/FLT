/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryPrincipalLiftCriterion
public import FLT.Mazur.SchemeQuasiCompactOpenKernelPower

/-!
# Original boundary numerators from equations on an open of the full relation

A raw original boundary lift need only satisfy the endpoint equation on a
specified relation open. Any original scalar whose full relation principal
open lies there produces an invariant numerator after a power. The relation
need not be affine, and all boundary equations retain their nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open SchemeEffectiveEpiSections InvariantOpenCoefficientRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [CompactSpace D]
  (J : A.IdealSheafData) (t : Γ(J.subscheme, ⊤))
  (a : Γ(A, ⊤)) (ha : J.subschemeι.appTop a = t)
  (O : D.Opens) (he : O.ι.appTop (p.appTop a) = O.ι.appTop (q.appTop a))

include ha he in
/-- Clear full relation equations to construct an exact original invariant boundary numerator. -/
theorem exists_pow_mem_originalBoundaryLiftIdeal_of_relation_open
    (s : compatibleFunctions p q) (hs : D.basicOpen (p.appTop s.val) ≤ O) :
    ∃ N : ℕ, s ^ N ∈ originalBoundaryLiftIdeal (p := p) (q := q) J t := by
  obtain ⟨N, hN⟩ := SchemeQuasiCompactOpenKernelPower.exists_pow_mul_eq_finite O.ι
    (p.appTop s.val) (fun _ : Unit ↦ p.appTop a) (fun _ : Unit ↦ q.appTop a)
    (by simpa only [Scheme.Opens.opensRange_ι] using hs) (fun _ ↦ he)
  have hw : s.val ^ N * a ∈ compatibleFunctions p q := by
    change p.appTop (s.val ^ N * a) = q.appTop (s.val ^ N * a)
    rw [map_mul, map_mul, map_pow, map_pow, ← s.property]
    exact hN ()
  refine ⟨N, ⟨⟨s.val ^ N * a, hw⟩, ?_⟩⟩
  change J.subschemeι.appTop (s.val ^ N * a) = J.subschemeι.appTop (s ^ N).val * t
  rw [map_mul, ha]
  rfl

include ha he in
/-- Divide the numerator to obtain a full invariant lift on the original principal open. -/
theorem exists_principalBoundaryLift_of_relation_open [IsAffine A] [QuasiSeparatedSpace D]
    (s : compatibleFunctions p q) (hs : D.basicOpen (p.appTop s.val) ≤ O) :
    ∃ u : coefficients p q (A.basicOpen s.val) (compatibleFunctions_basicOpen p q s),
      (J.comap (A.basicOpen s.val).ι).subschemeι.appTop u.val =
        (IdealSheafClosedTransitions.map (J.comap (A.basicOpen s.val).ι) J
          (A.basicOpen s.val).ι rfl).appTop t := by
  obtain ⟨N, hN⟩ := exists_pow_mem_originalBoundaryLiftIdeal_of_relation_open J t a ha O he s hs
  exact exists_principalBoundaryLift_of_pow s J t N hN

include ha in
/-- A boundary-zero change may solve the open equations while preserving the boundary. -/
theorem exists_pow_mem_originalBoundaryLiftIdeal_of_relation_correction
    (z : Γ(A, ⊤)) (hz : J.subschemeι.appTop z = 0)
    (heq : O.ι.appTop (p.appTop (a - z)) = O.ι.appTop (q.appTop (a - z)))
    (s : compatibleFunctions p q) (hs : D.basicOpen (p.appTop s.val) ≤ O) :
    ∃ N : ℕ, s ^ N ∈ originalBoundaryLiftIdeal (p := p) (q := q) J t := by
  apply exists_pow_mem_originalBoundaryLiftIdeal_of_relation_open J t (a - z) _ O heq s hs
  rw [map_sub, ha, hz, sub_zero]

end FLT.Mazur.EquivalenceRelationOrderedFrames
