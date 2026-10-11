/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorIdealStalkExt
public import FLT.Mazur.CoherentGenericIdealEmbedding

/-!
# Stalks of an integral scheme's image ideal

The full scheme-theoretic image ideal is the kernel of the actual stalk map
at points of an integral source. At a field stalk it is the maximal ideal.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
open AnnihilatorSubsheaf CoherentGenericIdealEmbedding
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y : Scheme.{u}} (p : Y ⟶ X) [QuasiCompact p] [IsIntegral Y]

/-- An integral source identifies its image-ideal stalk with the stalk-map kernel. -/
theorem stalkIdeal_image_eq_ker (y : Y) :
    stalkIdeal p.ker (p y) = RingHom.ker (p.stalkMap y).hom := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (p y))
      TopologicalSpace.isOpen_univ
  apply le_antisymm
  · rw [stalkIdeal_eq_map p.ker _ ⟨U, hU⟩ hy, Ideal.map_le_iff_le_comap]
    intro a ha
    change p.stalkMap y (X.presheaf.germ U _ hy a) = 0
    rw [Scheme.Hom.germ_stalkMap_apply]
    have hz : p.app U a = 0 := by
      simpa only [Scheme.Hom.ker_apply, RingHom.mem_ker] using ha
    rw [hz, map_zero]
  · intro r hr
    obtain ⟨V, hx, a, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
    let b := X.presheaf.map (homOfLE hWV).op a
    have hb : X.presheaf.germ W _ hxW b = X.presheaf.germ V _ hx a :=
      X.presheaf.germ_res_apply (homOfLE hWV) _ hxW a
    have hz : p.app W b = 0 := by
      apply germ_injective_of_isIntegral Y y hxW
      rw [map_zero, ← Scheme.Hom.germ_stalkMap_apply, hb]
      exact hr
    have hi : b ∈ p.ker.ideal ⟨W, hW⟩ := by
      simpa only [Scheme.Hom.ker_apply, RingHom.mem_ker] using hz
    rw [← hb, stalkIdeal_eq_map p.ker _ ⟨W, hW⟩ hxW]
    exact Ideal.mem_map_of_mem _ hi

/-- A field stalk on the source makes the image-ideal stalk maximal. -/
theorem stalkIdeal_image_eq_maximalIdeal (y : Y) (hy : IsField (Y.presheaf.stalk y)) :
    stalkIdeal p.ker (p y) = IsLocalRing.maximalIdeal (X.presheaf.stalk (p y)) := by
  let _ := hy.toField
  rw [stalkIdeal_image_eq_ker]
  have h := IsLocalRing.maximalIdeal_comap (p.stalkMap y).hom
  rw [IsLocalRing.maximalIdeal_eq_bot] at h
  exact h

end FLT.Mazur.FCurve
