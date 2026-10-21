/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAtlasPairTransfer

/-!
# Scheme-valued recognition of the full atlas-pair transition

Any two presentations of the same resolved pair factor through the full
transition domain. This applies to arbitrary coefficient schemes and
nonflat arithmetic inputs, without pointwise coordinate choices.
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
local notation "O" => atlasPairTransferOpen hπ data j hj a b c d
local notation "tr" => atlasPairTransfer hπ data j hj a b c d
variable {T : Scheme}
  (f : T ⟶ pullback (globalSmoothAtlasMap hπ data j hj a ≫
      (finiteGlobalStructure hπ data j hj).smoothLocus.ι ≫ finiteGlobalStructure hπ data j hj)
    (globalSmoothAtlasMap hπ data j hj b ≫
      (finiteGlobalStructure hπ data j hj).smoothLocus.ι ≫ finiteGlobalStructure hπ data j hj))
  (g : T ⟶ pullback (globalSmoothAtlasMap hπ data j hj c ≫
      (finiteGlobalStructure hπ data j hj).smoothLocus.ι ≫ finiteGlobalStructure hπ data j hj)
    (globalSmoothAtlasMap hπ data j hj d ≫
      (finiteGlobalStructure hπ data j hj).smoothLocus.ι ≫ finiteGlobalStructure hπ data j hj))
  (h : f ≫ finiteResolvedAtlasPairInput hπ data j hj a b =
    g ≫ finiteResolvedAtlasPairInput hπ data j hj c d)

include h in
/-- Equal resolved pairs lie in the whole transition domain over every coefficient scheme. -/
theorem atlasPairTransfer_lift_range : Set.range f ⊆ O := by
  rintro _ ⟨p, rfl⟩
  change input (f p) ∈ Set.range target
  refine ⟨g p, ?_⟩
  exact (congrArg (fun k => k p) h).symm

/-- The original pair presentation factors through the exact transition domain. -/
def atlasPairTransferLift : T ⟶ (O).toScheme :=
  IsOpenImmersion.lift (O).ι f (by
    rw [Scheme.Opens.range_ι]
    exact atlasPairTransfer_lift_range hπ data j hj a b c d f g h)

local notation "lift" => atlasPairTransferLift hπ data j hj a b c d f g h

/-- The factorization retains the whole original presentation. -/
@[reassoc] theorem atlasPairTransferLift_source : lift ≫ (O).ι = f :=
  IsOpenImmersion.lift_fac _ _ _

/-- The canonical simultaneous transition agrees with the supplied second presentation. -/
@[reassoc] theorem atlasPairTransferLift_target : lift ≫ tr = g := by
  apply (cancel_mono target).mp
  rw [Category.assoc, atlasPairTransfer_input, atlasPairTransferLift_source_assoc, h]

/-- Comparing both actual inputs suffices to recognize equal resolved pair presentations. -/
theorem atlasPairTransfer_pair_eq
    (h₁ : f ≫ pullback.fst ta tb ≫ chart a = g ≫ pullback.fst tc td ≫ chart c)
    (h₂ : f ≫ pullback.snd ta tb ≫ chart b = g ≫ pullback.snd tc td ≫ chart d) :
    f ≫ input = g ≫ target := by
  apply pullback.hom_ext
  · simpa only [Category.assoc, finiteResolvedAtlasPairInput_fst] using h₁
  · simpa only [Category.assoc, finiteResolvedAtlasPairInput_snd] using h₂

end FLT.Mazur.WeierstrassDividedDepth
