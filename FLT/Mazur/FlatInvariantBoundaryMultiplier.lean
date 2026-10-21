/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RingPairInvariantFlatScalars
public import FLT.Mazur.FlatSectionLiftIdeal

/-!
# Original boundary multipliers from branch-only invariant numerators

A numerator may live solely in the flat scalar extension. Its full endpoint
agreement identifies it with a new scalar. The exact flat lifting ideal then
recovers an original multiplier outside the contracted test ideal.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.FlatInvariantBoundaryMultiplier
open RingPairInvariantFlatScalars FlatAlgebraEqualizer
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A C B : Type*} [CommRing A] [CommRing C] [CommRing B]
  (p q : A →+* C)
local notation "R" => invariants p q
attribute [local instance] RingPairInvariantFlatScalars.sourceAlgebra
  RingPairInvariantFlatScalars.targetAlgebra

variable [Algebra (invariants p q) B]
  (f : A →ₐ[invariants p q] B)

variable (S : Type*) [CommRing S] [Algebra (invariants p q) S]
  [Module.Flat (invariants p q) S]

/-- A branch-only numerator puts its multiplier in the extended original lifting ideal. -/
theorem multiplier_mem (t : B) (s : S) (a : S ⊗[R] A)
    (he : tensorMap S (first p q) a = tensorMap S (second p q) a)
    (hb : tensorMap S f a =
      algebraMap S (S ⊗[R] B) s * (1 ⊗ₜ[R] t)) :
    s ∈ (sectionLiftIdeal (f.toRingHom.comp (invariants p q).subtype) t).map (algebraMap R S) := by
  obtain ⟨b, hba⟩ := scalarMap_surjective p q S ⟨a, he⟩
  have hval := congrArg Subtype.val hba
  change algebraMap S (S ⊗[R] A) b = a at hval
  rw [← hval, AlgHom.commutes] at hb
  rw [show f.toRingHom.comp (invariants p q).subtype = algebraMap R B from
    RingHom.ext f.commutes,
    FlatSectionLiftIdeal.ideal_map]
  exact ⟨b, hb⟩

/-- A nonvanishing branch multiplier constructs an actual original invariant boundary lift. -/
theorem exists_original_multiplier (P : Ideal S) (t : B) (s : S)
    (hs : s ∉ P) (a : S ⊗[R] A)
    (he : tensorMap S (first p q) a = tensorMap S (second p q) a)
    (hb : tensorMap S f a =
      algebraMap S (S ⊗[R] B) s * (1 ⊗ₜ[R] t)) :
    ∃ r : R, algebraMap R S r ∉ P ∧ ∃ w : R, f w.val = f r.val * t := by
  have hm := multiplier_mem p q f S t s a he hb
  by_contra h
  push Not at h
  apply hs
  apply Ideal.map_le_iff_le_comap.mpr (show
    sectionLiftIdeal (f.toRingHom.comp (invariants p q).subtype) t ≤
      P.comap (algebraMap R S) from ?_) hm
  intro r hr
  by_contra hn
  obtain ⟨w, hw⟩ := hr
  exact h r hn w hw

end FLT.Mazur.FlatInvariantBoundaryMultiplier
