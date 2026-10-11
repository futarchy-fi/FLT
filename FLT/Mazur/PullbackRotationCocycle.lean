/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PullbackRotationTransport

/-!
# Transport of overlap rotations by a pullback-preserving functor

Projection equations and cyclic identities survive the canonical pullback
comparisons. These abstract lemmas keep geometric reductions out of the proofs.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
  {A B E P Q T U V W : C}
  (l : A ⟶ E) (m : B ⟶ E) (n : P ⟶ T) (p : Q ⟶ T)
  (q : U ⟶ W) (s : V ⟶ W)
  [HasPullback l m] [HasPullback n p] [HasPullback q s]
  [HasPullback (F.map l) (F.map m)] [HasPullback (F.map n) (F.map p)]
  [HasPullback (F.map q) (F.map s)]
  [PreservesLimit (cospan l m) F] [PreservesLimit (cospan n p) F]
  [PreservesLimit (cospan q s) F]

/-- Canonical pullback transport preserves a proved rotation cocycle. -/
theorem mappedPullbackRotation_cocycle
    (r₁ : pullback l m ⟶ pullback n p) (r₂ : pullback n p ⟶ pullback q s)
    (r₃ : pullback q s ⟶ pullback l m) (h : r₁ ≫ r₂ ≫ r₃ = 𝟙 _) :
    mappedPullbackRotation F l m n p r₁ ≫ mappedPullbackRotation F n p q s r₂ ≫
      mappedPullbackRotation F q s l m r₃ = 𝟙 _ :=
  functorConjugate_cocycle F (PreservesPullback.iso F l m).symm
    (PreservesPullback.iso F n p).symm (PreservesPullback.iso F q s).symm r₁ r₂ r₃ h

end FLT.Mazur
