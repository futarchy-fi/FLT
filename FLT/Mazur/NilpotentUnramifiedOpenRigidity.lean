/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NilpotentClosedRestriction

/-!
# Infinitesimal uniqueness on an unramified open

Only the second map must land in the open. A nilpotent closed immersion
preserves points, so agreement there forces the first map into the same open.
Formal uniqueness then proves equality of the entire nonreduced maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.NilpotentUnramifiedOpenRigidity
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {T₀ T X S : Scheme} (i : T₀ ⟶ T) [IsClosedImmersion i]
  (hi : IsNilpotent i.ker) (f : X ⟶ S) (U : X.Opens)
  [FormallyUnramified (U.ι ≫ f)]

include hi in
/-- One endpoint in an unramified open suffices for full infinitesimal uniqueness. -/
theorem hom_ext {a b : T ⟶ X} (h : i ≫ a = i ≫ b)
    (hf : a ≫ f = b ≫ f) (hb : Set.range b ⊆ U) : a = b := by
  have ha : Set.range a ⊆ U := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨v, rfl⟩ := NilpotentClosedRestriction.surjective i hi t
    have he : a (i v) = b (i v) := congrArg (fun g : T₀ ⟶ X ↦ g v) h
    rw [he]
    exact hb (Set.mem_range_self _)
  have ha' : Set.range a ⊆ Set.range U.ι := by simpa using ha
  have hb' : Set.range b ⊆ Set.range U.ι := by simpa using hb
  let a' := IsOpenImmersion.lift U.ι a ha'
  let b' := IsOpenImmersion.lift U.ι b hb'
  have hA : a' ≫ U.ι = a := IsOpenImmersion.lift_fac _ _ _
  have hB : b' ≫ U.ι = b := IsOpenImmersion.lift_fac _ _ _
  have he : a' = b' := by
    apply FormallyUnramified.hom_ext i hi (U.ι ≫ f)
    · apply (cancel_mono U.ι).mp
      simpa only [Category.assoc, hA, hB] using h
    · simpa only [← Category.assoc, hA, hB] using hf
  rw [← hA, ← hB, he]

end FLT.Mazur.NilpotentUnramifiedOpenRigidity
