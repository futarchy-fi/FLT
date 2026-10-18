/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffinePullbackIdeal

/-!
# Actual ideal powers under arbitrary scheme base change

Local affine calculations glue without an affine, flat, or Noetherian
hypothesis on either scheme. In particular this applies to original rank-image
opens and arbitrary boundary coefficient schemes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.IdealSheafPowerPullback
open Scheme.IdealSheafData
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{0}}

/-- Every ideal power commutes with arbitrary pullback, retaining the entire ideal. -/
theorem comap_pow (I : X.IdealSheafData) (f : Y ⟶ X) (n : ℕ) :
    (I ^ n).comap f = I.comap f ^ n := by
  let C := {v : Y.affineOpens × X.affineOpens // v.1.1 ≤ f ⁻¹ᵁ v.2.1}
  let V : C → Y.affineOpens := fun v ↦ v.val.1
  have hV : ⨆ v, (V v).1 = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨_, ⟨W, hW, rfl⟩, hyW, _⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (f y)) isOpen_univ
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUW⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hyW (f ⁻¹ᵁ W).isOpen
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨(⟨U, hU⟩, ⟨W, hW⟩), hUW⟩, hyU⟩
  apply ext_of_iSup_eq_top V hV
  intro v
  rw [ideal_comap (I ^ n) f v.val.2 v.val.1 v.property]
  simp only [ideal_pow, Pi.pow_apply]
  change _ = ((I.comap f).ideal v.val.1) ^ n
  rw [ideal_comap I f v.val.2 v.val.1 v.property, Ideal.map_pow]

end FLT.Mazur.IdealSheafPowerPullback
