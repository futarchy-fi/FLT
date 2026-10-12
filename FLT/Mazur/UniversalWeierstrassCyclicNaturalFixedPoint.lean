/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicSliceRetraction
public import FLT.Mazur.UniversalWeierstrassCyclicNormalizationMap

/-!
# Sourcewise normalization fixes every natural normalized full family

Every pullback of the global normalized full point already lies in the actual
closed full slice. Independently evaluating normalization on that family fixes
its entire marking, including after any further source-scheme map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T : Scheme} (f : T ⟶ (cyclicAuxiliaryScheme n).left)

/-- Every natural full family is fixed by independently evaluated full normalization. -/
theorem cyclicNaturalNormalizedPoint_fixed :
    cyclicSchemeNormalizedPoint n (f ≫ cyclicNormalizationMap n) =
      f ≫ cyclicNormalizationMap n := by
  rw [← cyclicNaturalNormalizedSlicePoint_inclusion]
  exact cyclicSchemeNormalizedPoint_restrict n (cyclicNaturalNormalizedSlicePoint n f)

/-- Independent normalization recovers the exact natural full closed-slice point. -/
theorem cyclicNaturalNormalizedSlicePoint_fixed :
    cyclicSchemeNormalizedSlicePoint n (f ≫ cyclicNormalizationMap n) =
      cyclicNaturalNormalizedSlicePoint n f := by
  rw [← cyclicNaturalNormalizedSlicePoint_inclusion]
  exact cyclicSchemeNormalizedSlicePoint_restrict n (cyclicNaturalNormalizedSlicePoint n f)

/-- Every further pullback of a natural full family is fixed by independent normalization. -/
theorem cyclicNaturalNormalizedPoint_pullback_fixed {U : Scheme} (k : U ⟶ T) :
    cyclicSchemeNormalizedPoint n (k ≫ (f ≫ cyclicNormalizationMap n)) =
      k ≫ (f ≫ cyclicNormalizationMap n) := by
  rw [← Category.assoc]
  exact cyclicNaturalNormalizedPoint_fixed n (k ≫ f)

/-- Independent normalization on these full closed families commutes with every source map. -/
theorem cyclicNaturalNormalizedPoint_fixed_natural {U : Scheme} (k : U ⟶ T) :
    cyclicSchemeNormalizedPoint n (k ≫ (f ≫ cyclicNormalizationMap n)) =
      k ≫ cyclicSchemeNormalizedPoint n (f ≫ cyclicNormalizationMap n) := by
  rw [cyclicNaturalNormalizedPoint_fixed, cyclicNaturalNormalizedPoint_pullback_fixed]

end FLT.Mazur.UniversalWeierstrass
