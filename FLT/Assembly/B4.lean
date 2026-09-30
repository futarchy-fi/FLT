/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Assembly.ExistingInputs
public import FLT.Assembly.PrimePowerFinal
public import FLT.Assembly.PrimePowerSortingProof

/-!
# Frey reducibility from proved three-adic sorting

The public replacement for the legacy `FLT.Bosses.B4_proof` uses the proved
three-adic trace input. Integral lifting and compatible families remain admitted.
-/

@[expose] public section

namespace FLT.Bosses

/-- Frey torsion is reducible using proved sorting and the existing lifting/family inputs. -/
theorem B4_proof_from_sorting : B4 :=
  B4_of_inputs FLT.Assembly.hardlyRamifiedLifting
    FLT.Assembly.hardlyRamifiedCompatibleFamilies
    (ThreeAdicPlan.threeAdicFrobeniusTrace_of_primePowerSorting
      ThreeAdicPlan.primePowerSortedExtensionExists)

end FLT.Bosses
