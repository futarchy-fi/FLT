/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeCartierDivisorPullback
public import FLT.Mazur.CartierIdealPullbackComparison
public import FLT.Mazur.DivisorLineSectionSquare
public import FLT.Mazur.OverPullbackLocalPushout

/-!
# Relative Cartier comparisons under base change of a morphism

A morphism preserving two relative Cartier ideals continues to preserve them
under arbitrary base change. The induced positive line comparison commutes with
both base-change comparisons, including their canonical sections.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLinePullbackIsoOfEq
variable {S T : Scheme} {X Y : Over S} (f : X ⟶ Y) (g : T ⟶ S)
  (I : Y.left.IdealSheafData) (J : X.left.IdealSheafData)

/-- Pullback of the original ideal equality along the actual over-category square. -/
theorem relativeCartierMorphismBaseChange_ideal (h : I.comap f.left = J) :
    (I.comap (pullback.fst Y.hom g)).comap ((Over.pullback g).map f).left =
      J.comap (pullback.fst X.hom g) := by
  rw [← Scheme.IdealSheafData.comap_comp,
    (OverPullbackLocalPushout.map_isPullback g f).w,
    Scheme.IdealSheafData.comap_comp, h]

variable (hI : RelativeEffectiveCartier Y.hom I)
  (hJ : RelativeEffectiveCartier X.hom J) (h : I.comap f.left = J)

include hI hJ h in
/-- The canonical ideal comparison after base change is invertible, without flatness of `f`. -/
theorem relativeCartierMorphismBaseChange_isIso :
    IsIso (idealModulePullbackHom (I.comap (pullback.fst Y.hom g))
      ((Over.pullback g).map f).left) := by
  apply idealModulePullbackHom_isIso_of_cartier _
    (relativeCartierBaseChange Y.hom g I hI).1
  rw [relativeCartierMorphismBaseChange_ideal f g I J h]
  exact (relativeCartierBaseChange X.hom g J hJ).1

/-- The actual divisor-line comparison on the base-changed morphism. -/
irreducible_def relativeCartierMorphismBaseChangeIso :
    (Scheme.Modules.pullback ((Over.pullback g).map f).left).obj
      (divisorLineBundle (I.comap (pullback.fst Y.hom g))
        (relativeCartierBaseChange Y.hom g I hI).1) ≅
      divisorLineBundle (J.comap (pullback.fst X.hom g))
        (relativeCartierBaseChange X.hom g J hJ).1 := by
  let _ := relativeCartierMorphismBaseChange_isIso f g I J hI hJ h
  exact divisorLinePullbackIsoOfEq _ (relativeCartierBaseChange Y.hom g I hI).1
    (relativeCartierBaseChange X.hom g J hJ).1
    (relativeCartierMorphismBaseChange_ideal f g I J h)

/-- The new comparison preserves the actual pulled-back canonical section. -/
theorem relativeCartierMorphismBaseChangeIso_section :
    DivisorLineSectionCompatible ((Over.pullback g).map f).left
      (relativeCartierBaseChange Y.hom g I hI).1
      (relativeCartierBaseChange X.hom g J hJ).1
      (relativeCartierMorphismBaseChangeIso f g I J hI hJ h) := by
  let _ := relativeCartierMorphismBaseChange_isIso f g I J hI hJ h
  rw [relativeCartierMorphismBaseChangeIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- Base change commutes with any original section-preserving Cartier-line comparison. -/
theorem relativeCartierMorphismBaseChangeIso_square
    (e : (Scheme.Modules.pullback f.left).obj (divisorLineBundle I hI.1) ≅
      divisorLineBundle J hJ.1) (he : DivisorLineSectionCompatible f.left hI.1 hJ.1 e) :
    LinePullbackSquare ((Over.pullback g).map f).left (pullback.fst Y.hom g)
      (pullback.fst X.hom g) f.left (OverPullbackLocalPushout.map_isPullback g f).w
      (relativeCartierDivisorPullbackIso Y.hom g I hI)
      (relativeCartierMorphismBaseChangeIso f g I J hI hJ h)
      e (relativeCartierDivisorPullbackIso X.hom g J hJ) :=
  divisorLineSectionCompatible_square _ _ _ _ _
    (relativeCartierDivisorPullbackIso_section Y.hom g I hI)
    (relativeCartierMorphismBaseChangeIso_section f g I J hI hJ h) he
    (relativeCartierDivisorPullbackIso_section X.hom g J hJ)

end FLT.Mazur.FCurve
