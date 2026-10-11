/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AcyclicPointedAbelBaseChange

/-!
# Identity and composition for the intrinsic Abel correspondence

The independently constructed intrinsic pullback maps satisfy the functor
laws. Divisor equalities retain the entire ideal, while class equalities
are the actual Picard pullback laws. The last test base is unrestricted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CartierAbel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X S : Scheme.{0}} [IsLocallyNoetherian S]
  (f : X ⟶ S) [IsProper f] [Flat f]

/-- Identity base change fixes every intrinsic full divisor. -/
lemma acyclicRelativeDivisorPullback_id (D : AcyclicRankOneRelativeDivisor f) :
    acyclicRelativeDivisorPullback
      (IsPullback.of_horiz_isIso (show CommSq (𝟙 X) f f (𝟙 S) from ⟨by simp⟩)) D = D := by
  apply Subtype.ext
  apply Subtype.ext
  exact Scheme.IdealSheafData.comap_id D.val.val

/-- Identity base change fixes independently varying normalized intrinsic classes. -/
lemma acyclicPointedClassPullback_id (e : S ⟶ X) (c : AcyclicRankOnePointedClass f e) :
    acyclicPointedClassPullback
      (IsPullback.of_horiz_isIso (show CommSq (𝟙 X) f f (𝟙 S) from ⟨by simp⟩))
      e e (by simp) c = c := by
  apply Subtype.ext
  exact SchemePicard.pointedKernelPullback_id e c.val

variable {P T Q U : Scheme.{0}} [IsLocallyNoetherian T]
  {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ S}
  {r : Q ⟶ P} {a : Q ⟶ U} {k : U ⟶ T}
  [IsProper q] [Flat q] (h : IsPullback p q f g) (j : IsPullback r a q k)

/-- Iterated full-divisor pullback equals pullback along the pasted original square. -/
lemma acyclicRelativeDivisorPullback_comp (D : AcyclicRankOneRelativeDivisor f) :
    acyclicRelativeDivisorPullback j (acyclicRelativeDivisorPullback h D) =
      acyclicRelativeDivisorPullback (j.paste_horiz h) D := by
  apply Subtype.ext
  apply Subtype.ext
  exact (Scheme.IdealSheafData.comap_comp D.val.val r p).symm

/-- Iterated class pullback equals the class map of the pasted pointed square. -/
lemma acyclicPointedClassPullback_comp (e : S ⟶ X) (d : T ⟶ P) (b : U ⟶ Q)
    (hp : d ≫ p = g ≫ e) (hr : b ≫ r = k ≫ d)
    (c : AcyclicRankOnePointedClass f e) :
    acyclicPointedClassPullback j d b hr (acyclicPointedClassPullback h e d hp c) =
      acyclicPointedClassPullback (j.paste_horiz h) e b
        (by rw [← Category.assoc, hr, Category.assoc, hp, Category.assoc]) c := by
  apply Subtype.ext
  exact SchemePicard.pointedKernelPullback_comp e d p g hp b r k hr c.val

end FLT.Mazur.CartierAbel
