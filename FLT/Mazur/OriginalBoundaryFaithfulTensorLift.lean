/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryTensorLift
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Unscaled original boundary lifting from faithfully flat tensor solutions

Faithful flatness descends the entire boundary lifting problem, including
both full endpoint equations. The branch numerator need not be an original
section, and no finite generation or Noetherian scalar ring is required.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open SchemeEffectiveEpiSections RingPairInvariantFlatScalars FlatAlgebraEqualizer
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} (J : A.IdealSheafData)
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
variable (S : Type) [CommRing S] [Algebra (invariants p.appTop.hom q.appTop.hom) S]
  [Module.FaithfullyFlat (invariants p.appTop.hom q.appTop.hom) S]
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "α" => first p.appTop.hom q.appTop.hom
local notation "β" => second p.appTop.hom q.appTop.hom

/-- Full branch lifting is equivalent to lifting by an original invariant. -/
theorem originalBoundaryLift_iff_faithful_tensor (t : Γ(J.subscheme, ⊤)) :
    (∃ a : S ⊗[R] Γ(A, ⊤), tensorMap S α a = tensorMap S β a ∧
      tensorMap S (originalBoundaryMap J) a = 1 ⊗ₜ[R] t) ↔
    ∃ w : compatibleFunctions p q, J.subschemeι.appTop w.val = t := by
  constructor
  · rintro ⟨a, he, hb⟩
    have hm := FlatInvariantBoundaryMultiplier.multiplier_mem p.appTop.hom q.appTop.hom
      (originalBoundaryMap J) S t 1 a he (by simpa only [map_one, one_mul] using hb)
    let I : Ideal R := originalBoundaryLiftIdeal (p := p) (q := q) J t
    have hI : sectionLiftIdeal
        ((originalBoundaryMap (p := p) (q := q) J).toRingHom.comp (Subring.subtype R)) t =
        I := by
      ext r
      rfl
    rw [hI] at hm
    have hm' : (1 : R) ∈ (I.map (algebraMap R S)).comap (algebraMap R S) := by
      change algebraMap R S 1 ∈ I.map (algebraMap R S)
      simpa only [map_one] using hm
    rw [Ideal.comap_map_eq_self_of_faithfullyFlat] at hm'
    exact (one_mem_originalBoundaryLiftIdeal J t).mp hm'
  · rintro ⟨w, hw⟩
    refine ⟨1 ⊗ₜ[R] w.val, ?_, ?_⟩
    · change (1 : S) ⊗ₜ[R] p.appTop w.val = 1 ⊗ₜ[R] q.appTop w.val
      rw [w.property]
    · change (1 : S) ⊗ₜ[R] J.subschemeι.appTop w.val = 1 ⊗ₜ[R] t
      rw [hw]

end FLT.Mazur.EquivalenceRelationOrderedFrames
