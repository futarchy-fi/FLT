/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.Categories
public import Mathlib.RingTheory.DualNumber
public import Mathlib.Topology.Instances.TrivSqZeroExt

/-! # The finite dual-number test object with the original residue field -/

@[expose] public noncomputable section

open IsLocalRing TrivSqZeroExt

namespace Deformation.ProartinianCat

variable (O : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)]

local notation "k" => residueField (𝓞 := O)
local notation "D" => DualNumber k

instance dualNumber_discrete : DiscreteTopology D :=
  inferInstanceAs (DiscreteTopology (k × k))

instance dualNumber_finite : Finite D := by
  let : Finite k := inferInstanceAs (Finite (ResidueField O))
  exact inferInstanceAs (Finite (k × k))

/-- The coefficient map to the dual numbers is local. -/
instance dualNumber_isLocalHom : IsLocalHom (algebraMap O D) where
  map_nonunit a ha := by
    apply (isUnit_map_iff (algebraMap O k) a).mp
    simpa only [algebraMap_eq_inl', fst_inl] using
      (isUnit_iff_isUnit_fst.mp ha)

/-- The dual numbers have the prescribed residue field, with its original coefficient map. -/
instance dualNumber_isResidueAlgebra : IsResidueAlgebra O D where
  isSurjective' := by
    intro z
    obtain ⟨x, rfl⟩ := residue_surjective z
    obtain ⟨a, ha⟩ := residue_surjective (R := O) x.fst
    refine ⟨a, ?_⟩
    have hn : residue D (inr x.snd) = 0 :=
      (TrivSqZeroExt.isNilpotent_inr x.snd).map (residue D) |>.eq_zero
    have hx : x = inl x.fst + inr x.snd := (inl_fst_add_inr_snd_eq x).symm
    rw [IsScalarTower.algebraMap_apply O D (ResidueField D), algebraMap_eq_inl',
      show algebraMap O k a = x.fst from ha, hx, map_add, hn, add_zero]
    simp only [fst_add, fst_inl, fst_inr, add_zero]
    rfl

/-- Dual numbers over the original residue field, as a finite proartinian test object. -/
abbrev dualNumberTest : ProartinianCat O where
  carrier := D
  isLocalProartinianAlgebra := ⟨⟩

instance dualNumberTest_finite : Finite (dualNumberTest O) := inferInstanceAs (Finite D)

instance dualNumberTest_discrete : DiscreteTopology (dualNumberTest O) :=
  inferInstanceAs (DiscreteTopology D)

end Deformation.ProartinianCat
