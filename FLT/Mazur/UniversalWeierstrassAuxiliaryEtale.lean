/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryTorsionMarkingComparison
public import FLT.Mazur.UniversalWeierstrassAuxiliaryCoverage
public import FLT.Mazur.UniversalWeierstrassAuxiliaryFullBasis

/-!
# An actual etale cover carrying a full auxiliary basis

The original auxiliary marking scheme is etale and surjective over the
coefficient base. Its actual markings trivialize the full four-torsion scheme.
Thus auxiliary bases exist etale locally, and the resulting scheme basis
persists under arbitrary further base changes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

/-- The original level-four marking map is etale over the full coefficient base. -/
instance levelFour_etale : Etale levelFour.hom := by
  have : Etale (GroupTorsionScheme.scheme universalGroup 4).hom := fourTorsion_etale
  exact AuxiliaryTorsionMarkingComparison.faithfulScheme_etale universalGroup 4
    (Labels 4) (labels_pow 4)

/-- The constructed auxiliary parameter scheme is an actual etale covering family. -/
def auxiliaryEtaleCover : parameterBase.Cover (Scheme.precoverage @Etale) :=
  Scheme.Cover.mkOfCovers Unit (fun _ ↦ levelFour.left) (fun _ ↦ levelFour.hom)
    (fun s ↦ by obtain ⟨x, hx⟩ := levelFour.hom.surjective s; exact ⟨(), x, hx⟩)

/-- The full auxiliary basis is an isomorphism in schemes over the level scheme. -/
def auxiliaryFullBasisOver :
    Over.mk auxiliaryConstantLabelsMap ≅ Over.mk auxiliaryFourTorsionMap :=
  Over.isoMk auxiliaryFullBasis auxiliaryFullBasis_base

/-- The full basis remains a scheme isomorphism over every further test, including nilpotents. -/
def auxiliaryBaseChangedFullBasis {T : Scheme} (g : T ⟶ levelFour.left) :
    (Over.pullback g).obj (Over.mk auxiliaryConstantLabelsMap) ≅
      (Over.pullback g).obj (Over.mk auxiliaryFourTorsionMap) :=
  (Over.pullback g).mapIso auxiliaryFullBasisOver

end FLT.Mazur.UniversalWeierstrass
