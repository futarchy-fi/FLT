/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResolvedPairAtlas

/-!
# Simultaneous transition of the complete smooth atlas pair

The domain is the full inverse image of a second pair chart, with no
puncturing or contraction of either input. Both factors change together
and retain their exact resolved input morphisms.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  (a b c d : Fin (j + 3))
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "chart" => globalSmoothAtlasMap hπ data j hj
local notation "ta" => chart a ≫ t
local notation "tb" => chart b ≫ t
local notation "tc" => chart c ≫ t
local notation "td" => chart d ≫ t
local notation "input" => finiteResolvedAtlasPairInput hπ data j hj a b
local notation "target" => finiteResolvedAtlasPairInput hπ data j hj c d

/-- The entire overlap of two actual smooth chart pairs in the resolved product. -/
def atlasPairTransferOpen : (pullback ta tb).Opens := input ⁻¹ᵁ (target).opensRange

local notation "O" => atlasPairTransferOpen hπ data j hj a b c d

/-- Both target chart memberships, without any further condition, define the domain. -/
theorem atlasPairTransferOpen_mem (p : (pullback ta tb : Scheme)) :
    p ∈ O ↔ chart a (pullback.fst ta tb p) ∈ Set.range (chart c) ∧
      chart b (pullback.snd ta tb p) ∈ Set.range (chart d) := by
  change input p ∈ (target).opensRange ↔ _
  rw [finiteResolvedAtlasPairInput_opensRange]
  change (pullback.fst t t (input p) ∈ Set.range (chart c) ∧
    pullback.snd t t (input p) ∈ Set.range (chart d)) ↔ _
  have hfst := congrArg (fun f => f p)
    (finiteResolvedAtlasPairInput_fst hπ data j hj a b)
  have hsnd := congrArg (fun f => f p)
    (finiteResolvedAtlasPairInput_snd hπ data j hj a b)
  change pullback.fst t t (input p) = chart a (pullback.fst ta tb p) at hfst
  change pullback.snd t t (input p) = chart b (pullback.snd ta tb p) at hsnd
  rw [hfst, hsnd]

/-- Change both coordinates simultaneously on their complete overlap domain. -/
def atlasPairTransfer : (O).toScheme ⟶ pullback tc td :=
  IsOpenImmersion.lift target ((O).ι ≫ input) (by
    rintro _ ⟨p, rfl⟩
    exact p.property)

local notation "tr" => atlasPairTransfer hπ data j hj a b c d

/-- The transfer preserves the complete original resolved pair, as a scheme morphism. -/
@[reassoc] theorem atlasPairTransfer_input : tr ≫ target = (O).ι ≫ input :=
  IsOpenImmersion.lift_fac _ _ _

instance atlasPairTransfer_open : IsOpenImmersion tr := by
  unfold atlasPairTransfer
  infer_instance

/-- The first input is unchanged in the actual resolved smooth model. -/
@[reassoc] theorem atlasPairTransfer_first :
    tr ≫ pullback.fst tc td ≫ chart c = (O).ι ≫ pullback.fst ta tb ≫ chart a := by
  rw [← finiteResolvedAtlasPairInput_fst, atlasPairTransfer_input_assoc,
    finiteResolvedAtlasPairInput_fst]

/-- The second input is unchanged in the actual resolved smooth model. -/
@[reassoc] theorem atlasPairTransfer_second :
    tr ≫ pullback.snd tc td ≫ chart d = (O).ι ≫ pullback.snd ta tb ≫ chart b := by
  rw [← finiteResolvedAtlasPairInput_snd, atlasPairTransfer_input_assoc,
    finiteResolvedAtlasPairInput_snd]

/-- The transferred pair has the original coefficient point. -/
@[reassoc] theorem atlasPairTransfer_structure :
    tr ≫ pullback.fst tc td ≫ tc = (O).ι ≫ pullback.fst ta tb ≫ ta := by
  exact atlasPairTransfer_first_assoc hπ data j hj a b c d t

/-- Any pair map with these original ambient inputs is the constructed transition. -/
theorem atlasPairTransfer_unique (f : (O).toScheme ⟶ pullback tc td)
    (hf : f ≫ target = (O).ι ≫ input) : f = tr := by
  apply (cancel_mono target).mp
  exact hf.trans (atlasPairTransfer_input hπ data j hj a b c d).symm

end FLT.Mazur.WeierstrassDividedDepth
