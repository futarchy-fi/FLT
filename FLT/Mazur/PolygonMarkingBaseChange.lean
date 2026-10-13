/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSinglePointLineNormalization
public import FLT.Mazur.RelativeCartierDivisorPullback
public import FLT.Mazur.DivisorLineSectionCompatibility

/-!
# Original polygon marking lines over arbitrary parameter schemes

Pull back the actual marked Cartier ideal on the entire singular polygon.
Its positive line and canonical vanishing section have canonical comparisons
for every base map, including maps from nonreduced schemes.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonMarkingBaseChange
open PolygonPinching PolygonMarkedSections PolygonSinglePointLineNormalization FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  {T : Scheme} (g : T ⟶ Spec (.of K)) (a : Kˣ) (i : Fin n)

/-- The original marking ideal after arbitrary base change. -/
def markingIdeal : ((Over.pullback g).obj C).left.IdealSheafData :=
  (sectionMap K n p a i).ker.comap (pullback.fst C.hom g)

include h in
/-- The original marked Cartier divisor stays relative Cartier on the whole family. -/
theorem markingIdeal_cartier :
    RelativeEffectiveCartier ((Over.pullback g).obj C).hom (markingIdeal K n p g a i) :=
  relativeCartierBaseChange C.hom g _ (section_cartier K n p hn q h a i)

/-- Positive divisor line of the actual base-changed marking. -/
def markingLine : ((Over.pullback g).obj C).left.Modules :=
  divisorLineBundle (markingIdeal K n p g a i) (markingIdeal_cartier K n hn p q h g a i).1

/-- Canonical comparison with the pullback of the original positive marking line. -/
irreducible_def markingLineIso :
    (Scheme.Modules.pullback (pullback.fst C.hom g)).obj (pointLine K n hn p q h a i) ≅
      markingLine K n hn p q h g a i :=
  relativeCartierDivisorPullbackIso C.hom g _ (section_cartier K n p hn q h a i)

/-- The family comparison preserves the actual canonical vanishing section. -/
theorem markingLineIso_section :
    DivisorLineSectionCompatible (pullback.fst C.hom g)
      (section_cartier K n p hn q h a i).1 (markingIdeal_cartier K n hn p q h g a i).1
      (markingLineIso K n hn p q h g a i) := by
  rw [markingLineIso_def]
  exact relativeCartierDivisorPullbackIso_section _ _ _ _

end FLT.Mazur.PolygonMarkingBaseChange
