/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticZeroLabeledCompatibility

/-!
# Gluing on the original stage-zero arithmetic model

Maps on the full labeled charts glue uniquely once the four constructed
standard endpoint equations hold. The result is a map from the original
resolved arithmetic stage, with all its original chart restrictions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ)
local notation "c" => arithmeticLabeledAtlasMap hπ data H m 0 (Nat.zero_le n)
local notation "U" => arithmeticLabeledOpenCover hπ data H m 0 (Nat.zero_le n)
local notation "X" => finiteGlobalArithmeticStage hπ data 0 (Nat.zero_le n) m
variable {Y : Scheme.{0}}
  (f : ∀ i, arithmeticLabeledAtlasObject hπ data H m 0 (Nat.zero_le n) i ⟶ Y)
  (hI : arithmeticInitialInfinityCompatible hπ data H m 0 (Nat.zero_le n) f)
  (hT : arithmeticZeroTerminalCompatible hπ data m H f)

/-- Glue the four full labeled maps using their explicit original standard endpoint equations. -/
def arithmeticZeroLabeledDesc : X ⟶ Y :=
  (U).glueMorphisms f (arithmeticZeroLabeled_compatible hπ data H m f hI hT)

/-- Gluing recovers every original labeled chart map. -/
@[reassoc] theorem arithmeticZeroLabeledDesc_chart (i : ArithmeticChartLabel 0) :
    c i ≫ arithmeticZeroLabeledDesc hπ data H m f hI hT = f i :=
  (U).ι_glueMorphisms _ _ i

/-- Full stage-zero maps are detected on the actual four labeled charts. -/
theorem arithmeticZeroLabeled_hom_ext (g h : X ⟶ Y)
    (he : ∀ i, c i ≫ g = c i ≫ h) : g = h :=
  (U).hom_ext g h he

/-- A global map with the prescribed chart restrictions equals the constructed gluing. -/
theorem arithmeticZeroLabeledDesc_unique (g : X ⟶ Y) (hg : ∀ i, c i ≫ g = f i) :
    g = arithmeticZeroLabeledDesc hπ data H m f hI hT := by
  apply arithmeticZeroLabeled_hom_ext hπ data H m
  intro i
  exact (hg i).trans (arithmeticZeroLabeledDesc_chart hπ data H m f hI hT i).symm

include hI hT in
/-- The four original standard endpoint equations give the unique actual stage-zero morphism. -/
theorem arithmeticZeroLabeledDesc_existsUnique : ∃! g : X ⟶ Y, ∀ i, c i ≫ g = f i := by
  refine ⟨arithmeticZeroLabeledDesc hπ data H m f hI hT, ?_, ?_⟩
  · exact arithmeticZeroLabeledDesc_chart hπ data H m f hI hT
  · intro g hg
    exact arithmeticZeroLabeledDesc_unique hπ data H m f hI hT g hg

end FLT.Mazur.WeierstrassDividedDepth
