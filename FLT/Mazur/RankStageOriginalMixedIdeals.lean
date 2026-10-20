/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageOriginalMixedTests

/-!
# One fixed original ideal for both mixed endpoints

The original relation square identifies the two pulled rank ideals before
any choice of order. Thus every closed reduction has the same exact kernel
at both endpoints, not merely the same reduced support.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A]
  (e : CategoryTheory.EquivalenceRelation p q) (n : ℕ)
local instance mixedIdealOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance mixedIdealOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance mixedIdealOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable {T : Scheme.{0}} (g g' : T ⟶ (rankImageOpen (Over.mk p) n).toScheme)
  (δ : T ⟶ D) (hδ : δ ≫ p = g ≫ (rankImageOpen (Over.mk p) n).ι)
  (hδ' : δ ≫ q = g' ≫ (rankImageOpen (Over.mk p) n).ι)
local notation "U" => rankImageOpen (Over.mk p) n
local notation "I" => rankStratumIdeal (Over.mk p) n

include e hδ hδ' in
/-- The two independent original endpoints pull back exactly the same rank ideal. -/
theorem rankStage_original_mixed_ideal : (I).comap g = (I).comap g' := by
  let z := (rankOpenFirst_isPullback (p := p) n).lift δ g hδ
  have hz : z ≫ (p ⁻¹ᵁ U).ι = δ :=
    (rankOpenFirst_isPullback (p := p) n).lift_fst _ _ _
  have hf : z ≫ rankOpenFirst (p := p) n = g :=
    (rankOpenFirst_isPullback (p := p) n).lift_snd _ _ _
  have hs : z ≫ rankOpenSecond e n = g' := by
    apply (cancel_mono (U).ι).mp
    rw [Category.assoc, rankOpenSecond, Scheme.Hom.resLE_comp_ι,
      ← Category.assoc, hz, hδ']
  calc
    (I).comap g = ((I).comap (rankOpenFirst (p := p) n)).comap z := by
      rw [← Scheme.IdealSheafData.comap_comp, hf]
    _ = ((I).comap (rankOpenSecond e n)).comap z := by rw [rankIdeal_invariant e n]
    _ = (I).comap g' := by rw [← Scheme.IdealSheafData.comap_comp, hs]

include e hδ hδ' in
/-- All orders of the two original mixed reductions have one exact coefficient kernel. -/
theorem rankStage_original_mixed_kernels [IsAffine T] (k : ℕ) :
    RingHom.ker ((((I).comap g) ^ k).subschemeι.appTop.hom) =
      RingHom.ker ((((I).comap g') ^ k).subschemeι.appTop.hom) := by
  rw [IdealSheafClosedCoreTests.test_kernel, IdealSheafClosedCoreTests.test_kernel,
    rankStage_original_mixed_ideal e n g g' δ hδ hδ']

end FLT.Mazur.EquivalenceRelationOrderedFrames
