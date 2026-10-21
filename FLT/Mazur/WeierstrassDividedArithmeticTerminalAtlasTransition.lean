/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTerminalAtlasInputs
public import FLT.Mazur.WeierstrassDividedArithmeticAtlasTestTransition

/-!
# The explicit terminal boundary transfer in the full smooth integral atlas

Restrict the actual boundary pair to its full simultaneous smooth preimage.
Its source and target have identical smooth domains and realize the canonical
integral transition, with both entire arithmetic input morphisms preserved.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
  arithmeticRetainedTensorIso olderSuccessiveTensorAtlasIso finiteTensorAtlasObject
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m j : ℕ) (hj : j + 1 ≤ n)
  (b : Fin (j + 1 + 3))
local notation "Q" => PolygonArithmeticStages.Quotient R π m
local notation "a" => (Fin.succ ⟨j + 1 - j, by omega⟩ : Fin (j + 1 + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m (j + 1) hj
local notation "s" => finiteGlobalArithmeticStructure hπ data (j + 1) hj m
local notation "base" => finiteGlobalStructure hπ data (j + 1) hj
local notation "projection" => pullback.fst base
  (Spec.map (CommRingCat.ofHom (algebraMap R Q)))
local notation "old" => finiteArithmeticNewestTensorChart hπ data m j hj
local notation "O" => arithmeticTerminalPairOpen hπ data m j hj (chart b ≫ s)
local notation "x" => arithmeticTerminalAtlasSourceFirst hπ data m j hj b
local notation "y" => arithmeticTerminalAtlasSourceSecond hπ data m j hj b
local notation "z" => arithmeticTerminalAtlasTargetFirst hπ data m j hj b
local notation "w" => arithmeticTerminalAtlasTargetSecond hπ data m j hj b
local notation "h₁" => arithmeticTerminalAtlasInputs_first hπ data m j hj b
local notation "h₂" => congrArg (fun f => f ≫ chart b)
  (arithmeticTerminalAtlasInputs_second hπ data m j hj b)
local notation "h" => arithmeticTerminalAtlasInputs_base hπ data m j hj b

/-- The full smooth domain of the original explicit boundary pair. -/
def arithmeticTerminalAtlasSmoothOpen :=
  arithmeticAtlasTestOpen hπ data m (j + 1) hj a b x y

local notation "D" => arithmeticTerminalAtlasSmoothOpen hπ data m j hj b

/-- Smooth restriction retains exactly both original global smooth inputs. -/
theorem arithmeticTerminalAtlasSmoothOpen_eq :
    D = ((O).ι ≫ pullback.fst (old ≫ s) (chart b ≫ s) ≫ old ≫ projection) ⁻¹ᵁ
      (base).smoothLocus ⊓
      ((O).ι ≫ pullback.snd (old ≫ s) (chart b ≫ s) ≫ chart b ≫ projection) ⁻¹ᵁ
        (base).smoothLocus := by
  rw [arithmeticTerminalAtlasSmoothOpen, arithmeticAtlasTestOpen_eq]
  simp only [arithmeticTerminalAtlasSourceFirst, arithmeticTerminalAtlasSourceSecond,
    Category.assoc]
  rw [arithmeticBoundaryAtlas_newest_assoc hπ data m j hj]

/-- The explicit target has precisely the same simultaneous smooth preimage. -/
theorem arithmeticTerminalAtlasSmoothOpen_target :
    D = arithmeticAtlasTestOpen hπ data m (j + 1) hj 1 b z w :=
  arithmeticAtlasTestTransition_open hπ data m (j + 1) hj a b 1 b x y z w h₁ h₂

/-- The original explicit boundary pair realizes the full integral atlas transition. -/
def arithmeticTerminalAtlasTransition :
    (D).toScheme ⟶ (atlasPairTransferOpen hπ data (j + 1) hj a b 1 b).toScheme :=
  arithmeticAtlasTestTransition hπ data m (j + 1) hj a b 1 b x y z w h₁ h₂ h

/-- The integral source is the exact original arithmetic boundary presentation. -/
@[reassoc] theorem arithmeticTerminalAtlasTransition_source :
    arithmeticTerminalAtlasTransition hπ data m j hj b ≫
      (atlasPairTransferOpen hπ data (j + 1) hj a b 1 b).ι =
      arithmeticAtlasTestPair hπ data m (j + 1) hj a b x y h ≫
        arithmeticAtlasPairPresentation hπ data m (j + 1) hj a b :=
  arithmeticAtlasTestTransition_source hπ data m (j + 1) hj a b 1 b x y z w h₁ h₂ h

/-- The transferred integral pair is exactly the original explicit boundary target. -/
@[reassoc] theorem arithmeticTerminalAtlasTransition_target :
    arithmeticTerminalAtlasTransition hπ data m j hj b ≫
      atlasPairTransfer hπ data (j + 1) hj a b 1 b =
      arithmeticAtlasTestTarget hπ data m (j + 1) hj a b 1 b x y z w h₁ h₂ h ≫
        arithmeticAtlasPairPresentation hπ data m (j + 1) hj 1 b :=
  arithmeticAtlasTestTransition_target hπ data m (j + 1) hj a b 1 b x y z w h₁ h₂ h

end FLT.Mazur.WeierstrassDividedDepth
