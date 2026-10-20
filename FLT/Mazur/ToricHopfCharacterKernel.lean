/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# The character kernel of a toric Hopf quotient

Characters are the actual images of monomials in the given coordinate map.
Distinct characters in the quotient by its kernel remain linearly independent,
including in positive characteristic and for nonreduced coordinate algebras.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.ToricHopfCharacterKernel

variable {K G A : Type*} [Field K] [Group G] [Ring A] [HopfAlgebra K A]
  (f : MonoidAlgebra K G →ₐc[K] A)

/-- Restriction of the original coordinate map to the actual monomial characters. -/
def character : G →* GroupLike K A where
  toFun g := ⟨f (MonoidAlgebra.single g 1),
    (MonoidAlgebra.isGroupLikeElem_single_one g).map f⟩
  map_one' := by
    apply GroupLike.val_injective
    exact map_one f
  map_mul' g h := by
    apply GroupLike.val_injective
    change f (MonoidAlgebra.single (g * h) 1) =
      f (MonoidAlgebra.single g 1) * f (MonoidAlgebra.single h 1)
    simpa only [MonoidAlgebra.single_mul_single, one_mul] using
      map_mul f (MonoidAlgebra.single g 1) (MonoidAlgebra.single h 1)

/-- Characters trivial on the original subgroup, defined from its full coordinate algebra. -/
abbrev kernel : Subgroup G := (character f).ker

/-- Equality in the character kernel is equality in the entire coordinate algebra. -/
theorem mem_kernel_iff (g : G) :
    g ∈ kernel f ↔ f (MonoidAlgebra.single g 1) = 1 := by
  change character f g = 1 ↔ _
  exact GroupLike.val_inj.symm

/-- The faithful remaining characters after dividing by the actual kernel. -/
def quotientCharacter : G ⧸ kernel f →* GroupLike K A :=
  QuotientGroup.kerLift (character f)

/-- The quotient character keeps the image of each original monomial. -/
theorem quotientCharacter_mk (g : G) :
    (quotientCharacter f (QuotientGroup.mk g)).val = f (MonoidAlgebra.single g 1) := rfl

/-- No two remaining characters become equal in the original coordinate algebra. -/
theorem quotientCharacter_injective : Function.Injective (quotientCharacter f) :=
  QuotientGroup.kerLift_injective (character f)

/-- Remaining characters are independent even for a nonreduced finite subgroup. -/
theorem quotientCharacter_linearIndependent :
    LinearIndependent K (fun g => (quotientCharacter f g).val) :=
  linearIndep_groupLikeVal.comp _ (quotientCharacter_injective f)

/-- A finite coordinate algebra has only finitely many remaining characters. -/
theorem quotient_finite [Module.Finite K A] : Finite (G ⧸ kernel f) :=
  (quotientCharacter_linearIndependent f).finite

end FLT.Mazur.ToricHopfCharacterKernel
