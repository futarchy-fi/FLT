/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAtlasPairUnequalAddition
public import FLT.Mazur.WeierstrassDividedAtlasPairTransfer

/-!
# Existing unequal-depth outputs through simultaneous full atlas transitions

Pull the constructed unequal-depth addition through the exact transition
of both integral atlas factors. The result is an actual smooth output on
an open of the original full pair, with its original coefficient point.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] globalIntegralAtlasObject globalIntegralAtlasMap
  globalSmoothAtlasOpen globalSmoothAtlasMap finiteGlobalModel finiteGlobalStructure
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n k l : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (j : ℕ) (hj : j ≤ n)
  (a b : Fin (j + 3)) (d : Data W π k) (e : Data W π l) (hkl : k ≤ l)
  (hdj : l - k ≤ j)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
variable (f : globalIntegralAtlasObject data j hj a ⟶ chart d)
  (g : globalIntegralAtlasObject data j hj b ⟶ chart e)
variable
  (hf : f ≫ Spec.map (CommRingCat.ofHom
    (algebraMap R (Coordinate W (π ^ k) d.b3 d.b4 d.b6))) =
      globalIntegralAtlasMap hπ data j hj a ≫ finiteGlobalStructure hπ data j hj)
  (hg : g ≫ Spec.map (CommRingCat.ofHom
    (algebraMap R (Coordinate W (π ^ l) e.b3 e.b4 e.b6))) =
      globalIntegralAtlasMap hπ data j hj b ≫ finiteGlobalStructure hπ data j hj)
variable (a₀ b₀ : Fin (j + 3))
local notation "O" => atlasPairTransferOpen hπ data j hj a₀ b₀ a b
local notation "tr" => atlasPairTransfer hπ data j hj a₀ b₀ a b
local notation "V" => atlasPairUnequalOpen hπ data j hj a b d e hkl hdj f g hf hg
local notation "add" => atlasPairUnequalAddition hπ data j hj a b d e hkl hdj f g hf hg

/-- The complete inverse image of the constructed unequal-depth output domain. -/
def transferredUnequalOpen : (O).toScheme.Opens := tr ⁻¹ᵁ V

local notation "P" => transferredUnequalOpen hπ data j hj a b d e hkl hdj f g hf hg a₀ b₀

/-- An actual smooth output after changing both original integral input charts. -/
def transferredUnequalAddition : (P).toScheme ⟶ (U).toScheme := (tr ∣_ V) ≫ add

local notation "output" =>
  transferredUnequalAddition hπ data j hj a b d e hkl hdj f g hf hg a₀ b₀

/-- The transferred domain is an actual open input in the complete resolved product. -/
def transferredUnequalInput : (P).toScheme ⟶ finiteResolvedProduct hπ data j hj :=
  (P).ι ≫ (O).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a₀ b₀

instance transferredUnequalInput_open : IsOpenImmersion
    (transferredUnequalInput hπ data j hj a b d e hkl hdj f g hf hg a₀ b₀) := by
  unfold transferredUnequalInput
  infer_instance

/-- The output has the first original input's coefficient point, before either transition. -/
@[reassoc] theorem transferredUnequalAddition_structure :
    output ≫ t = (P).ι ≫ (O).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a₀ b₀ ≫
      pullback.fst t t ≫ t := by
  rw [transferredUnequalAddition, Category.assoc, atlasPairUnequalAddition_structure,
    morphismRestrict_ι_assoc, atlasPairTransfer_input_assoc]
  rfl

/-- The same output has the second original input's coefficient point. -/
@[reassoc] theorem transferredUnequalAddition_structure_snd :
    output ≫ t = (P).ι ≫ (O).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a₀ b₀ ≫
      pullback.snd t t ≫ t := by
  rw [transferredUnequalAddition_structure, pullback.condition]

end FLT.Mazur.WeierstrassDividedDepth
