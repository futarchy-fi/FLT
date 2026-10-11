/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AcyclicPointedAbelEquivalence
public import FLT.Mazur.AcyclicRankOneBaseChange
public import FLT.Mazur.PointedPicardKernelPullback
public import FLT.Mazur.PointNormalizedDivisorBaseChange

/-!
# Naturality of the intrinsic acyclic pointed Abel map

Both intrinsic classes and full relative divisors pull back from a proper
flat family over a locally Noetherian base to every cartesian test. The Abel
map commutes with these actual pullbacks. Lines vary independently on the
original family; they are not restricted to one fixed coefficient bundle.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CartierAbel
open FCurve SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {P X T S : Scheme.{0}} [IsLocallyNoetherian S]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsProper f] [Flat f] (h : IsPullback p q f g)
  (e : S ⟶ X) (d : T ⟶ P) (hp : d ≫ p = g ≫ e)

/-- Pullback of independently varying intrinsic pointed classes to an unrestricted test. -/
def acyclicPointedClassPullback (c : AcyclicRankOnePointedClass f e) :
    AcyclicRankOnePointedClass q d := by
  refine ⟨pointedKernelPullback e d p g hp c.val, ?_⟩
  obtain ⟨L, hL, hc, hA⟩ := c.property
  refine ⟨(Scheme.Modules.pullback p).obj L, hL.pullback p, ?_,
    acyclicRankOne_baseChange h L hL hA⟩
  exact congrArg (SchemePicard.pullback p) hc

/-- The intrinsic class map is exactly the original Picard pullback. -/
lemma acyclicPointedClassPullback_class (c : AcyclicRankOnePointedClass f e) :
    (acyclicPointedClassPullback h e d hp c).val.val =
      SchemePicard.pullback p c.val.val := rfl

/-- Actual full relative Cartier divisors with the intrinsic line condition pull back. -/
def acyclicRelativeDivisorPullback (D : AcyclicRankOneRelativeDivisor f) :
    AcyclicRankOneRelativeDivisor q := by
  let hD : RelativeEffectiveCartier f D.val.val := ⟨D.val.property, D.property.1⟩
  let E := pointedDivisorPullback h D.val hD
  let _ := relativeCartierIdealPullback_originalSquare h D.val.val hD
  refine ⟨E, (relativeCartier_originalSquare h D.val.val hD).2, ?_⟩
  apply (acyclicRankOne_iso q
    (divisorLinePullbackIsoOfEq p D.val.property E.property rfl)).mp
  exact acyclicRankOne_baseChange h _ D.val.property.divisorLineBundle_locallyFreeRankOne
    D.property.2

/-- The new divisor retains the complete ideal comap, including multiplicities. -/
lemma acyclicRelativeDivisorPullback_ideal (D : AcyclicRankOneRelativeDivisor f) :
    (acyclicRelativeDivisorPullback h D).val.val = D.val.val.comap p := rfl

/-- The intrinsic Abel map commutes with pullback on every compatible pointed test. -/
theorem acyclicPointedAbel_natural (he : e ≫ f = 𝟙 S) (hd : d ≫ q = 𝟙 T)
    (D : AcyclicRankOneRelativeDivisor f) :
    acyclicPointedAbel q d hd (acyclicRelativeDivisorPullback h D) =
      acyclicPointedClassPullback h e d hp (acyclicPointedAbel f e he D) := by
  apply Subtype.ext
  apply Subtype.ext
  exact pointedDivisorClass_pullback h e he d hd hp D.val
    ⟨D.val.property, D.property.1⟩

end FLT.Mazur.CartierAbel
