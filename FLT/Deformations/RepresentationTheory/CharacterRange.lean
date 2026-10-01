/-
Copyright (c) 2026 Kelvin Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelvin Santos
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Algebra.Field.Basic

/-!
# Characters factored through a cyclic image

A character trivial on the kernel of a homomorphism factors through its image.
Every generator of that image detects a nontrivial character. For quadratic
characters with values in a field, the detected value is minus one.
-/

@[expose] public section

namespace MonoidHom

variable {G A B : Type*} [Group G] [Group A] [Group B]
  (ε : G →* A) (χ : G →* B)

/-- Factor a character through the image of a homomorphism whose kernel it kills. -/
noncomputable def factorThroughRange (h : ε.ker ≤ χ.ker) : ε.range →* B :=
  (QuotientGroup.lift ε.ker χ h).comp
    (QuotientGroup.quotientKerEquivRange ε).symm.toMonoidHom

@[simp]
theorem factorThroughRange_apply (h : ε.ker ≤ χ.ker) (g : G) :
    ε.factorThroughRange χ h (ε.rangeRestrict g) = χ g := by
  change QuotientGroup.lift ε.ker χ h
    ((QuotientGroup.quotientKerEquivRange ε).symm
      ((QuotientGroup.quotientKerEquivRange ε) (QuotientGroup.mk g))) = χ g
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The factor of a nontrivial character is nontrivial. -/
theorem factorThroughRange_ne_one (h : ε.ker ≤ χ.ker) (hχ : χ ≠ 1) :
    ε.factorThroughRange χ h ≠ 1 := by
  intro hf
  apply hχ
  ext g
  have := congrArg (fun f : ε.range →* B ↦ f (ε.rangeRestrict g)) hf
  simpa using this

/-- A homomorphism on a generated cyclic group is detected by the generator. -/
theorem apply_ne_one_of_generator {C : Type*} [Group C]
    (ψ : C →* B) (hψ : ψ ≠ 1) (c : C)
    (hc : ∀ x : C, x ∈ Subgroup.zpowers c) : ψ c ≠ 1 := by
  intro h
  apply hψ
  ext x
  obtain ⟨n, rfl⟩ := hc x
  simp [h]

/-- Any lift of a generator of the image detects a nontrivial character. -/
theorem apply_ne_one_of_range_generator (h : ε.ker ≤ χ.ker) (hχ : χ ≠ 1)
    (g : G) (hg : ∀ x : ε.range, x ∈ Subgroup.zpowers (ε.rangeRestrict g)) :
    χ g ≠ 1 := by
  simpa using (ε.factorThroughRange χ h).apply_ne_one_of_generator
    (ε.factorThroughRange_ne_one χ h hχ) (ε.rangeRestrict g) hg

variable {k : Type*} [Field k]

/-- A quadratic character takes the value minus one at every lift of an image
 generator. The conclusion holds even in characteristic two, where the
 nontriviality and quadratic hypotheses cannot simultaneously hold. -/
theorem quadratic_eq_neg_one_of_range_generator (χ : G →* kˣ)
    (h : ε.ker ≤ χ.ker) (hχ : χ ≠ 1) (hsq : ∀ g, χ g ^ 2 = 1)
    (g : G) (hg : ∀ x : ε.range, x ∈ Subgroup.zpowers (ε.rangeRestrict g)) :
    χ g = -1 := by
  have hne := ε.apply_ne_one_of_range_generator χ h hχ g hg
  apply Units.ext
  apply (sq_eq_one_iff.mp (show (χ g : k) ^ 2 = 1 by
    exact congrArg (fun u : kˣ ↦ (u : k)) (hsq g))).resolve_left
  intro hval
  exact hne (Units.ext hval)

/-- A cyclic image supplies a detecting element for any nontrivial quadratic
character trivial on the kernel. -/
theorem exists_quadratic_eq_neg_one [IsCyclic ε.range] (χ : G →* kˣ)
    (h : ε.ker ≤ χ.ker) (hχ : χ ≠ 1) (hsq : ∀ g, χ g ^ 2 = 1) :
    ∃ g : G, χ g = -1 := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := ε.range)
  obtain ⟨g, hg⟩ := ε.rangeRestrict_surjective a
  exact ⟨g, ε.quadratic_eq_neg_one_of_range_generator χ h hχ hsq g (hg ▸ ha)⟩

end MonoidHom
