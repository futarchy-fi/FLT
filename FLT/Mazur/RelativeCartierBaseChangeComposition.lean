/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeCartierMorphismBaseChange
public import FLT.Mazur.OverPullbackSectionComposition

/-!
# Cartier lines under successive arbitrary base changes

The canonical comparison of the original iterated fiber product with the
fiber product over the composite base map preserves the full Cartier ideal.
The resulting line comparison commutes with the two actual base-change maps.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLinePullbackIsoOfEq
variable {S T U : Scheme} (X : Over S) (g : T ⟶ S) (k : U ⟶ T)
  (I : X.left.IdealSheafData) (hI : RelativeEffectiveCartier X.hom I)

/-- The canonical composition chart preserves the entire original relative Cartier ideal. -/
theorem relativeCartierBaseChangeComposition_ideal :
    (I.comap (pullback.fst X.hom (k ≫ g))).comap
        ((Over.pullbackComp k g).inv.app X).left =
      (I.comap (pullback.fst X.hom g)).comap
        (pullback.fst ((Over.pullback g).obj X).hom k) := by
  rw [← Scheme.IdealSheafData.comap_comp, OverPullbackSection.comp_inv_fst,
    Scheme.IdealSheafData.comap_comp]

/-- Actual positive-line comparison on the canonical composition chart. -/
irreducible_def relativeCartierBaseChangeCompositionIso :
    (Scheme.Modules.pullback ((Over.pullbackComp k g).inv.app X).left).obj
      (divisorLineBundle (I.comap (pullback.fst X.hom (k ≫ g)))
        (relativeCartierBaseChange X.hom (k ≫ g) I hI).1) ≅
      divisorLineBundle ((I.comap (pullback.fst X.hom g)).comap
        (pullback.fst ((Over.pullback g).obj X).hom k))
        (relativeCartierBaseChange ((Over.pullback g).obj X).hom k _
          (relativeCartierBaseChange X.hom g I hI)).1 := by
  let _ : IsIso ((Over.pullbackComp k g).inv.app X).left :=
    inferInstanceAs (IsIso ((Over.forget _).map ((Over.pullbackComp k g).inv.app X)))
  exact divisorLinePullbackIsoOfEq _ (relativeCartierBaseChange X.hom (k ≫ g) I hI).1
    (relativeCartierBaseChange ((Over.pullback g).obj X).hom k _
      (relativeCartierBaseChange X.hom g I hI)).1
    (relativeCartierBaseChangeComposition_ideal X g k I)

/-- The actual composition chart preserves the canonical section. -/
theorem relativeCartierBaseChangeCompositionIso_section :
    DivisorLineSectionCompatible ((Over.pullbackComp k g).inv.app X).left
      (relativeCartierBaseChange X.hom (k ≫ g) I hI).1
      (relativeCartierBaseChange ((Over.pullback g).obj X).hom k _
        (relativeCartierBaseChange X.hom g I hI)).1
      (relativeCartierBaseChangeCompositionIso X g k I hI) := by
  let _ : IsIso ((Over.pullbackComp k g).inv.app X).left :=
    inferInstanceAs (IsIso ((Over.forget _).map ((Over.pullbackComp k g).inv.app X)))
  rw [relativeCartierBaseChangeCompositionIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- Successive base changes and direct base change give the same actual line comparison. -/
theorem relativeCartierBaseChangeCompositionIso_square :
    LinePullbackSquare (pullback.fst ((Over.pullback g).obj X).hom k)
      (pullback.fst X.hom g) ((Over.pullbackComp k g).inv.app X).left
      (pullback.fst X.hom (k ≫ g)) (OverPullbackSection.comp_inv_fst k g X).symm
      (relativeCartierDivisorPullbackIso X.hom g I hI)
      (relativeCartierDivisorPullbackIso ((Over.pullback g).obj X).hom k _
        (relativeCartierBaseChange X.hom g I hI))
      (relativeCartierDivisorPullbackIso X.hom (k ≫ g) I hI)
      (relativeCartierBaseChangeCompositionIso X g k I hI) :=
  divisorLineSectionCompatible_square _ _ _ _ _
    (relativeCartierDivisorPullbackIso_section X.hom g I hI)
    (relativeCartierDivisorPullbackIso_section ((Over.pullback g).obj X).hom k _
      (relativeCartierBaseChange X.hom g I hI))
    (relativeCartierDivisorPullbackIso_section X.hom (k ≫ g) I hI)
    (relativeCartierBaseChangeCompositionIso_section X g k I hI)

end FLT.Mazur.FCurve
