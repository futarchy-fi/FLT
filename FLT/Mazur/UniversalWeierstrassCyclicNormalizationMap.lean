/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicNormalizedSlice

/-!
# The global full normalization morphism and its natural source families

Apply actual full normalization to the universal full point. Its unique lift
to the closed full slice gives an actual global morphism. Composition supplies
natural full families, whose auxiliary factor is the existing source normalization.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n]

/-- The actual universal full normalization morphism into the original full marking scheme. -/
def cyclicNormalizationMap : (cyclicAuxiliaryScheme n).left ⟶ (cyclicAuxiliaryScheme n).left :=
  cyclicSchemeNormalizedPoint n (𝟙 _)

/-- The global full normalization factors through the actual closed full slice. -/
def cyclicNormalizationSliceMap : (cyclicAuxiliaryScheme n).left ⟶ cyclicNormalizedSlice n :=
  cyclicSchemeNormalizedSlicePoint n (𝟙 _)

/-- The closed-slice factorization retains the global complete marking. -/
@[reassoc] theorem cyclicNormalizationSliceMap_inclusion :
    cyclicNormalizationSliceMap n ≫ cyclicNormalizedSliceInclusion n =
      cyclicNormalizationMap n :=
  cyclicSchemeNormalizedSlicePoint_inclusion n (𝟙 _)

/-- The auxiliary factor of the global full map is the actual auxiliary normalization. -/
@[reassoc] theorem cyclicNormalizationMap_forget :
    cyclicNormalizationMap n ≫ (forgetCyclic n).left =
      auxiliarySchemeNormalizedPoint (forgetCyclic n).left := by
  have h := cyclicSchemeNormalizedPoint_forget n (𝟙 _)
  simp only [cyclicSchemeAuxiliaryPoint, Category.id_comp] at h
  exact h

/-- A full source family gives its natural normalized full closed-slice point. -/
def cyclicNaturalNormalizedSlicePoint {T : Scheme}
    (f : T ⟶ (cyclicAuxiliaryScheme n).left) : T ⟶ cyclicNormalizedSlice n :=
  f ≫ cyclicNormalizationSliceMap n

/-- The natural closed-slice family retains its actual global full parameter. -/
@[reassoc] theorem cyclicNaturalNormalizedSlicePoint_inclusion {T : Scheme}
    (f : T ⟶ (cyclicAuxiliaryScheme n).left) :
    cyclicNaturalNormalizedSlicePoint n f ≫ cyclicNormalizedSliceInclusion n =
      f ≫ cyclicNormalizationMap n := by
  rw [cyclicNaturalNormalizedSlicePoint, Category.assoc,
    cyclicNormalizationSliceMap_inclusion]

/-- Natural full normalization retains precisely the original auxiliary source normalization. -/
@[reassoc] theorem cyclicNaturalNormalizedSlicePoint_forget {T : Scheme}
    (f : T ⟶ (cyclicAuxiliaryScheme n).left) :
    cyclicNaturalNormalizedSlicePoint n f ≫ cyclicNormalizedSliceInclusion n ≫
      (forgetCyclic n).left = auxiliarySchemeNormalizedPoint (cyclicSchemeAuxiliaryPoint n f) := by
  rw [← Category.assoc, cyclicNaturalNormalizedSlicePoint_inclusion,
    Category.assoc, cyclicNormalizationMap_forget,
    ← auxiliarySchemeNormalizedPoint_natural]
  rfl

/-- Complete normalized slice families commute with every source-scheme map. -/
@[reassoc] theorem cyclicNaturalNormalizedSlicePoint_natural {T U : Scheme}
    (f : T ⟶ (cyclicAuxiliaryScheme n).left) (k : U ⟶ T) :
    cyclicNaturalNormalizedSlicePoint n (k ≫ f) =
      k ≫ cyclicNaturalNormalizedSlicePoint n f :=
  Category.assoc _ _ _

/-- The auxiliary closed-slice point also agrees with the original source normalization. -/
@[reassoc] theorem cyclicNaturalNormalizedSlicePoint_auxiliary {T : Scheme}
    (f : T ⟶ (cyclicAuxiliaryScheme n).left) :
    cyclicNaturalNormalizedSlicePoint n f ≫ cyclicNormalizedSliceAuxiliary n =
      auxiliarySchemeNormalizedSlicePoint (cyclicSchemeAuxiliaryPoint n f) := by
  apply (cancel_mono normalizedSliceInclusion).mp
  rw [Category.assoc, ← cyclicNormalizedSlice_square,
    cyclicNaturalNormalizedSlicePoint_forget, auxiliarySchemeNormalizedSlicePoint_inclusion]

end FLT.Mazur.UniversalWeierstrass
