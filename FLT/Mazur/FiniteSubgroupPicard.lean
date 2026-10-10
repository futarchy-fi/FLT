/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveDivisorPullback
public import FLT.Mazur.CompatibleSubgroupAmple
public import FLT.Mazur.RelativePicardQuotient

/-!
# Picard classes of actual finite subgroup divisors

The positive divisor sheaf of a Cartier subgroup defines absolute and relative
Picard classes. Their comparison maps use the actual subgroup ideal under base
change and compatible curve isomorphisms.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

open FCurve

variable {S T : Scheme} {E : GeneralizedEllipticCurve S} {n : ℕ}
  (H : E.FiniteSubgroup n) (hI : EffectiveCartier H.ideal)

/-- The actual positive subgroup divisor in the Picard group of its curve. -/
def divisorPicardClass : SchemePicard.Pic E.curve.left :=
  SchemePicard.mk (divisorLineBundle H.ideal hI) hI.divisorLineBundle_locallyFreeRankOne

/-- The same subgroup divisor modulo line bundles pulled back from the base. -/
def divisorRelativePicardClass : SchemePicard.RelativePic E.curve.hom :=
  SchemePicard.relativeClass E.curve.hom (H.divisorPicardClass hI)

/-- Arbitrary base change pulls back the actual subgroup's Picard class. -/
theorem divisorPicardClass_baseChange (g : T ⟶ S) :
    (H.baseChange g).divisorPicardClass (H.effectiveCartier_baseChange hI g) =
      SchemePicard.pullback (pullback.fst E.curve.hom g) (H.divisorPicardClass hI) := by
  let := H.idealPullbackHom_isIso hI g
  exact SchemePicard.mk_eq_of_iso _ _
    (divisorLinePullbackIsoOfEq (pullback.fst E.curve.hom g) hI
      (H.effectiveCartier_baseChange hI g) (H.baseChange_ideal g).symm).symm

/-- The relative Picard comparison also retains the actual divisor class. -/
theorem divisorRelativePicardClass_baseChange (g : T ⟶ S) :
    (H.baseChange g).divisorRelativePicardClass (H.effectiveCartier_baseChange hI g) =
      SchemePicard.relativeMap (pullback.snd E.curve.hom g) E.curve.hom
        (pullback.fst E.curve.hom g) g pullback.condition.symm
        (H.divisorRelativePicardClass hI) := by
  change SchemePicard.relativeClass _ _ = SchemePicard.relativeClass _ _
  rw [divisorPicardClass_baseChange]

variable {H} {F : GeneralizedEllipticCurve S} {J : F.FiniteSubgroup n}

/-- Compatible subgroup isomorphisms identify the actual positive divisor classes. -/
theorem CompatibleIso.divisorPicardClass (a : CompatibleIso H J)
    (hJ : EffectiveCartier J.ideal) :
    J.divisorPicardClass hJ =
      SchemePicard.pullback a.curve.inv.curve.left (H.divisorPicardClass hI) := by
  have : IsIso a.curve.inv.curve.left :=
    inferInstanceAs (IsIso ((forgetCurve ⋙ Over.forget S).map a.curve.inv))
  have hi := ideal_transport H J a.curve a.subgroup a.compatible
  exact SchemePicard.mk_eq_of_iso _ _
    (divisorLinePullbackIsoOfEq a.curve.inv.curve.left hI hJ hi.symm).symm

/-- Compatible isomorphisms preserve the relative subgroup divisor class. -/
theorem CompatibleIso.divisorRelativePicardClass (a : CompatibleIso H J)
    (hJ : EffectiveCartier J.ideal) :
    J.divisorRelativePicardClass hJ =
      SchemePicard.relativeMap F.curve.hom E.curve.hom a.curve.inv.curve.left
        (𝟙 S) (by simp) (H.divisorRelativePicardClass hI) := by
  change SchemePicard.relativeClass _ _ = SchemePicard.relativeClass _ _
  rw [a.divisorPicardClass hI hJ]

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
