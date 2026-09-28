/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Assembly.PrimePowerSorting
public import FLT.GaloisRepresentation.HardlyRamified.CategoryDClassification
public import FLT.GroupScheme.SortedCanonicalFactorFiltration

/-!
# Integral sorting at every three-power level

The classification of simple category-D objects gives an integral canonical
factor filtration for every category-D object. Adjacent interchange sorts its
factors, and composition assembles the boundary into a sorted extension.
Neither step requires the whole object to be killed by three.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

/-- Every three-primary category-D object has an integral sorted extension. -/
theorem primePowerSortedExtensionExists : PrimePowerSortedExtensionExists := by
  intro H hD
  obtain ⟨factors, hF, hfactors⟩ := canonicalFactorFiltrationExists simpleDThree H hD
  obtain ⟨n, m, hsort⟩ := hF.sortCanonicalFactors hfactors
  exact sortedExtensionOfConstantThenMultiplicative n m hsort

/-- Integral sorting determines every character satisfying the three-adic conditions. -/
theorem threeAdicCharacterPurity : ThreeAdicCharacterPurity :=
  threeAdicCharacterPurity_of_primePowerSorting primePowerSortedExtensionExists

end ThreeAdicPlan
