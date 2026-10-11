/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityAtlasFamily
public import FLT.Mazur.WeierstrassDividedPositiveEqualityIndexedDescRecovery
import all FLT.Mazur.WeierstrassDividedPositiveEqualityAtlasFamily

/-!
# The positive-start family recovers the complete original atlas

Specializing the constructed descents to the actual cyclic components gives
all original atlas inclusions, including the distinct initial chart and s = 0.
This recovery statement does not assert global compatibility for arbitrary families.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp
local notation "F" => fun i => Over.Hom.left (Z i)
local notation "w" => positiveEqualityCycleComponent_scheme_endpoints hπ data D s hs hstart hk hp

/-- The chosen atlas family recovers every original inclusion for the actual cyclic components. -/
theorem positiveEqualityCycleAtlasFamily_original (i : Fin (s + 1 + 3)) :
    positiveEqualityCycleAtlasFamily hπ data D s hs hstart hk hp F w i =
      globalTensorAtlasMap hπ data K (s + 1) hs i := by
  by_cases h0 : i = 0
  · subst i
    rw [positiveEqualityCycleAtlasFamily_infinity]
    have H := positiveEqualityCycleInfinityDesc_eq_restriction
      hπ data D s hs hstart hk hp F (𝟙 _) (Category.comp_id _)
    simpa only [Category.comp_id] using H.symm
  by_cases h1 : i = Fin.succ 0
  · subst i
    rw [positiveEqualityCycleAtlasFamily_terminal]
    have H := positiveEqualityCycleTerminalAtlasDesc_eq_restriction
      hπ data D s hs hstart hk hp F (𝟙 _) (Category.comp_id _)
    simpa only [Category.comp_id] using H.symm
  by_cases hl : i = ⟨s + 3, by omega⟩
  · subst i
    rw [positiveEqualityCycleAtlasFamily_initial, positiveEqualityInitialIndexedDesc_original]
  by_cases h2 : i = ⟨2, by omega⟩
  · subst i
    rw [positiveEqualityCycleAtlasFamily_terminal_retained,
      positiveEqualityCycleTerminalIndexedDesc_original]
  have hi0 : i.val ≠ 0 := fun h => h0 (Fin.ext h)
  have hi1 : i.val ≠ 1 := fun h => h1 (Fin.ext h)
  have hil : i.val ≠ s + 3 := fun h => hl (Fin.ext h)
  have hi2 : i.val ≠ 2 := fun h => h2 (Fin.ext h)
  let j : Fin s := ⟨s + 2 - i.val, by omega⟩
  have hi : i = ⟨s - j.val + 2, by omega⟩ := by
    apply Fin.ext
    dsimp [j]
    omega
  rw [hi, positiveEqualityCycleAtlasFamily_positive,
    positiveEqualityCycleInteriorIndexedDesc_original]

end FLT.Mazur.WeierstrassDividedDepth
