/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticAdjacentAtlasInputs
public import FLT.Mazur.WeierstrassDividedArithmeticAtlasTestTransition

/-!
# The explicit adjacent boundary transfer in the full smooth integral atlas

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
  (hjNext : j + 2 ≤ n) (r : ℕ) (hr : j + 2 + r ≤ n) (b : Fin (j + 2 + r + 3))
local notation "Q" => PolygonArithmeticStages.Quotient R π m
local notation "k" => j + 2 + r
local notation "a" => (Fin.succ ⟨k - j, by omega⟩ : Fin (k + 3))
local notation "c" => (Fin.succ ⟨r + 1, by omega⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hr
local notation "s" => finiteGlobalArithmeticStructure hπ data k hr m
local notation "base" => finiteGlobalStructure hπ data k hr
local notation "projection" => pullback.fst base
  (Spec.map (CommRingCat.ofHom (algebraMap R Q)))
local notation "old" => finiteArithmeticAdjacentOldTensorChart hπ data m j hj r hr
local notation "O" => arithmeticAdjacentPairOpen hπ data m j hj r hr (chart b ≫ s)
local notation "x" => arithmeticAdjacentAtlasSourceFirst hπ data m j hj r hr b
local notation "y" => arithmeticAdjacentAtlasSourceSecond hπ data m j hj r hr b
local notation "z" => arithmeticAdjacentAtlasTargetFirst hπ data m j hj hjNext r hr b
local notation "w" => arithmeticAdjacentAtlasTargetSecond hπ data m j hj hjNext r hr b
local notation "h₁" => arithmeticAdjacentAtlasInputs_first hπ data m j hj hjNext r hr b
local notation "h₂" => congrArg (fun f => f ≫ chart b)
  (arithmeticAdjacentAtlasInputs_second hπ data m j hj hjNext r hr b)
local notation "h" => arithmeticAdjacentAtlasInputs_base hπ data m j hj r hr b

/-- The full smooth domain of the original explicit boundary pair. -/
def arithmeticAdjacentAtlasSmoothOpen :=
  arithmeticAtlasTestOpen hπ data m k hr a b x y

local notation "D" => arithmeticAdjacentAtlasSmoothOpen hπ data m j hj r hr b

/-- Smooth restriction retains exactly both original global smooth inputs. -/
theorem arithmeticAdjacentAtlasSmoothOpen_eq :
    D = ((O).ι ≫ pullback.fst (old ≫ s) (chart b ≫ s) ≫ old ≫ projection) ⁻¹ᵁ
      (base).smoothLocus ⊓
      ((O).ι ≫ pullback.snd (old ≫ s) (chart b ≫ s) ≫ chart b ≫ projection) ⁻¹ᵁ
        (base).smoothLocus := by
  rw [arithmeticAdjacentAtlasSmoothOpen, arithmeticAtlasTestOpen_eq]
  simp only [arithmeticAdjacentAtlasSourceFirst, arithmeticAdjacentAtlasSourceSecond,
    Category.assoc]
  rw [arithmeticBoundaryAtlas_adjacent_assoc hπ data m j hj r hr]

/-- The explicit target has precisely the same simultaneous smooth preimage. -/
theorem arithmeticAdjacentAtlasSmoothOpen_target :
    D = arithmeticAtlasTestOpen hπ data m k hr c b z w :=
  arithmeticAtlasTestTransition_open hπ data m k hr a b c b x y z w h₁ h₂

/-- The original explicit boundary pair realizes the full integral atlas transition. -/
def arithmeticAdjacentAtlasTransition :
    (D).toScheme ⟶ (atlasPairTransferOpen hπ data k hr a b c b).toScheme :=
  arithmeticAtlasTestTransition hπ data m k hr a b c b x y z w h₁ h₂ h

/-- The integral source is the exact original arithmetic boundary presentation. -/
@[reassoc] theorem arithmeticAdjacentAtlasTransition_source :
    arithmeticAdjacentAtlasTransition hπ data m j hj hjNext r hr b ≫
      (atlasPairTransferOpen hπ data k hr a b c b).ι =
      arithmeticAtlasTestPair hπ data m k hr a b x y h ≫
        arithmeticAtlasPairPresentation hπ data m k hr a b :=
  arithmeticAtlasTestTransition_source hπ data m k hr a b c b x y z w h₁ h₂ h

/-- The transferred integral pair is exactly the original explicit boundary target. -/
@[reassoc] theorem arithmeticAdjacentAtlasTransition_target :
    arithmeticAdjacentAtlasTransition hπ data m j hj hjNext r hr b ≫
      atlasPairTransfer hπ data k hr a b c b =
      arithmeticAtlasTestTarget hπ data m k hr a b c b x y z w h₁ h₂ h ≫
        arithmeticAtlasPairPresentation hπ data m k hr c b :=
  arithmeticAtlasTestTransition_target hπ data m k hr a b c b x y z w h₁ h₂ h

end FLT.Mazur.WeierstrassDividedDepth
