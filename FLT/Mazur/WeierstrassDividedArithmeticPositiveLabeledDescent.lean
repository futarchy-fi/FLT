/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticPositiveLabeledCompatibility

/-!
# Gluing on the original positive-retention arithmetic model

Maps on the full labeled charts glue uniquely once the constructed cyclic
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
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
local notation "c" => arithmeticLabeledAtlasMap hπ data H m (j + 1) hj
local notation "U" => arithmeticLabeledOpenCover hπ data H m (j + 1) hj
local notation "X" => finiteGlobalArithmeticStage hπ data (j + 1) hj m
variable {Y : Scheme.{0}}
  (f : ∀ i, arithmeticLabeledAtlasObject hπ data H m (j + 1) hj i ⟶ Y)
  (hInf : arithmeticInitialInfinityCompatible hπ data H m (j + 1) hj f)
  (hI : arithmeticPositiveInitialCompatible hπ data H m j hj f)
  (hA : arithmeticPositiveAdjacentCompatible hπ data H m j hj f)
  (hT : arithmeticPositiveTerminalCompatible hπ data H m j hj f)

/-- Glue the full labeled maps using their explicit original standard endpoint equations. -/
def arithmeticPositiveLabeledDesc : X ⟶ Y :=
  (U).glueMorphisms f (arithmeticPositiveLabeled_compatible hπ data H m j hj f hInf hI hA hT)

/-- Gluing recovers every original labeled chart map. -/
@[reassoc] theorem arithmeticPositiveLabeledDesc_chart (i : ArithmeticChartLabel (j + 1)) :
    c i ≫ arithmeticPositiveLabeledDesc hπ data H m j hj f hInf hI hA hT = f i :=
  (U).ι_glueMorphisms _ _ i

/-- Full positive-retention maps are detected on the actual labeled charts. -/
theorem arithmeticPositiveLabeled_hom_ext (g h : X ⟶ Y)
    (he : ∀ i, c i ≫ g = c i ≫ h) : g = h :=
  (U).hom_ext g h he

/-- A global map with the prescribed chart restrictions equals the constructed gluing. -/
theorem arithmeticPositiveLabeledDesc_unique (g : X ⟶ Y) (hg : ∀ i, c i ≫ g = f i) :
    g = arithmeticPositiveLabeledDesc hπ data H m j hj f hInf hI hA hT := by
  apply arithmeticPositiveLabeled_hom_ext hπ data H m j hj
  intro i
  exact (hg i).trans (arithmeticPositiveLabeledDesc_chart hπ data H m j hj f hInf hI hA hT i).symm

include hInf hI hA hT in
/-- The original cyclic edge equations give the unique actual positive-retention morphism. -/
theorem arithmeticPositiveLabeledDesc_existsUnique : ∃! g : X ⟶ Y, ∀ i, c i ≫ g = f i := by
  refine ⟨arithmeticPositiveLabeledDesc hπ data H m j hj f hInf hI hA hT, ?_, ?_⟩
  · exact arithmeticPositiveLabeledDesc_chart hπ data H m j hj f hInf hI hA hT
  · intro g hg
    exact arithmeticPositiveLabeledDesc_unique hπ data H m j hj f hInf hI hA hT g hg

end FLT.Mazur.WeierstrassDividedDepth
