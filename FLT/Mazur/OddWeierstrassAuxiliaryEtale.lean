/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryTorsionMarkingComparison
public import FLT.Mazur.OddWeierstrassAuxiliaryCoverage
public import FLT.Mazur.OddWeierstrassAuxiliaryFullBasis

/-!
# An actual etale cover carrying a full auxiliary basis

The original auxiliary marking scheme is etale and surjective over the
coefficient base. Its actual markings trivialize the full three-torsion scheme.
Thus auxiliary bases exist etale locally, and the resulting scheme basis
persists under arbitrary further base changes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.OddWeierstrassParameter

open IntegralWeierstrassParameter (OddChartRing)
open UniversalWeierstrass (Labels labels_pow)

/-- The original level-three marking map is etale over the full coefficient base. -/
instance levelThree_etale : Etale levelThree.hom := by
  have : Etale (GroupTorsionScheme.scheme universalGroup 3).hom := threeTorsion_etale
  exact AuxiliaryTorsionMarkingComparison.faithfulScheme_etale universalGroup 3
    (Labels 3) (labels_pow 3)

/-- The constructed auxiliary parameter scheme is an actual etale covering family. -/
def auxiliaryEtaleCover : parameterBase.Cover (Scheme.precoverage @Etale) :=
  Scheme.Cover.mkOfCovers Unit (fun _ ↦ levelThree.left) (fun _ ↦ levelThree.hom)
    (fun s ↦ by obtain ⟨x, hx⟩ := levelThree.hom.surjective s; exact ⟨(), x, hx⟩)

/-- The full auxiliary basis is an isomorphism in schemes over the level scheme. -/
def auxiliaryFullBasisOver :
    Over.mk auxiliaryConstantLabelsMap ≅ Over.mk auxiliaryThreeTorsionMap :=
  Over.isoMk auxiliaryFullBasis auxiliaryFullBasis_base

/-- The full basis remains a scheme isomorphism over every further test, including nilpotents. -/
def auxiliaryBaseChangedFullBasis {T : Scheme} (g : T ⟶ levelThree.left) :
    (Over.pullback g).obj (Over.mk auxiliaryConstantLabelsMap) ≅
      (Over.pullback g).obj (Over.mk auxiliaryThreeTorsionMap) :=
  (Over.pullback g).mapIso auxiliaryFullBasisOver

end FLT.Mazur.OddWeierstrassParameter
