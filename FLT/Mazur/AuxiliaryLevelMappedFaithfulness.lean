/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryLevelFaithfulRepresentation

/-!
# Testing universal faithfulness after composition of bases

Every test scheme mapping to a composed relative object itself lies over the
intermediate base. Thus testing all schemes over that base detects universal
faithfulness over the original base, without any affine or reducedness assumption.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.AuxiliaryLevel

variable {S B : Scheme} (b : B ⟶ S) (E : Over S) [GrpObj E]
  (A : Type) [Group A] [Fintype A] (T : Over B)

/-- Tests over the intermediate base suffice for universal faithfulness. -/
theorem universallyFaithful_of_mapped_tests
    (f : (Over.map b).obj T ⟶ homScheme E A)
    (hf : ∀ (U : Over B) (k : U ⟶ T), Nonempty U.left →
      Function.Injective (markingOf E A ((Over.map b).map k ≫ f))) :
    UniversallyFaithful E A f := by
  intro V k hV
  let U : Over B := Over.mk (k.left ≫ T.hom)
  let j : U ⟶ T := Over.homMk k.left rfl
  have hU : Nonempty U.left := hV
  intro a c hac
  apply hf U j hU
  apply Over.OverMorphism.ext
  have h := congrArg (fun q => q.left) hac
  exact h

end FLT.Mazur.AuxiliaryLevel
