/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointNormalizedDivisorFiber
public import FLT.Mazur.PointNormalizedLineBaseChange
public import FLT.Mazur.RelativeCartierOriginalSquare

/-!
# Pointed divisor fibers under arbitrary cartesian base change

The full ideal comap determines the changed divisor. The actual divisor-line
comparison and normalization comparison identify its pointed class, and
construct pullback on the pointed fibers without assumptions on the test base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open FCurve SchemePicard
variable {P X T S : Scheme.{0}} {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)
  (d : T ⟶ P) (hd : d ≫ q = 𝟙 T) (hp : d ≫ p = g ≫ e)

/-- Pull back the entire Cartier divisor along the actual supplied cartesian family square. -/
def pointedDivisorPullback (D : Divisor X) (hD : RelativeEffectiveCartier f D.val) :
    Divisor P :=
  ⟨D.val.comap p, (relativeCartier_originalSquare h D.val hD).1⟩

include hp in
/-- The original full divisor pullback has the pullback of the original normalized Picard class. -/
theorem pointedDivisorClass_pullback (D : Divisor X)
    (hD : RelativeEffectiveCartier f D.val) :
    (pointedDivisorClass q d hd (pointedDivisorPullback h D hD)).val =
      SchemePicard.pullback p (pointedDivisorClass f e he D).val := by
  let _ := relativeCartierIdealPullback_originalSquare h D.val hD
  have hi := mk_eq_of_iso ((D.property.divisorLineBundle_locallyFreeRankOne).pullback p)
    (relativeCartier_originalSquare h D.val hD).1.divisorLineBundle_locallyFreeRankOne
    (divisorLinePullbackIsoOfEq p D.property (relativeCartier_originalSquare h D.val hD).1 rfl)
  rw [pointedDivisorClass_eq, pointedDivisorClass_eq]
  change normalize q d (mk _ _) = pullback p (normalize f e (mk _ _))
  dsimp only [pointedDivisorPullback]
  rw [← hi]
  exact (pointNormalizedLine_baseChange_class f e q d p g h.w hp _
    D.property.divisorLineBundle_locallyFreeRankOne).symm

/-- The original pointed normalized fiber pulls back on every compatible pointed test family. -/
def pointedRelativeFiberPullback (L : X.Modules) (hL : LocallyFreeRankOne L)
    (D : PointedRelativeFiber f e he L hL) :
    PointedRelativeFiber q d hd ((Scheme.Modules.pullback p).obj L) (hL.pullback p) := by
  let hD : RelativeEffectiveCartier f D.val.val := ⟨D.val.property, D.property.1⟩
  refine ⟨pointedDivisorPullback h D.val hD,
    (relativeCartier_originalSquare h D.val.val hD).2, ?_⟩
  apply Subtype.ext
  rw [pointedDivisorClass_pullback h e he d hd hp D.val hD,
    congrArg Subtype.val D.property.2]
  exact pointNormalizedLine_baseChange_class f e q d p g h.w hp L hL

/-- Pullback on the pointed fiber preserves the full ideal comap, not only the support. -/
lemma pointedRelativeFiberPullback_ideal (L : X.Modules) (hL : LocallyFreeRankOne L)
    (D : PointedRelativeFiber f e he L hL) :
    (pointedRelativeFiberPullback h e he d hd hp L hL D).val.val = D.val.val.comap p := rfl

end FLT.Mazur.CartierAbel
