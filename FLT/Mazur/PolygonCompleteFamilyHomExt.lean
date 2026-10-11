/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteAdicIdealSeparation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Original stages detect morphisms of the complete family

The closed equalizer of two maps has an ideal contained in every parameter
power. Full ideal separation therefore makes that equalizer the whole family.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] originalStageToCompatibleProj exactVeroneseProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Original infinitesimal restrictions determine a map into any separated scheme. -/
theorem completeFamilyHom_ext_stages {Y : Scheme} [Y.IsSeparated]
    (f g : exactVeroneseProj K n h ⟶ Y)
    (hs : ∀ m, originalStageToCompatibleProj K n h m ≫ f =
      originalStageToCompatibleProj K n h m ≫ g) : f = g := by
  have hk : (equalizer.ι f g).ker = ⊥ := by
    apply completeIdeal_eq_bot_of_le_powers K n h
    intro m
    have hm := (equalizer.lift (originalStageToCompatibleProj K n h m) (hs m)).le_ker_comp
      (equalizer.ι f g)
    rw [equalizer.lift_ι, ← originalStageAdicIso_hom_ι,
      Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι] at hm
    exact hm
  have : IsIso (equalizer.ι f g) := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hk
  exact (cancel_epi (equalizer.ι f g)).mp (equalizer.condition f g)

/-- Isomorphisms of the complete family retain uniqueness from the actual original stages. -/
theorem completeFamilyIso_ext_stages {Y : Scheme} [Y.IsSeparated]
    (e e' : exactVeroneseProj K n h ≅ Y)
    (hs : ∀ m, originalStageToCompatibleProj K n h m ≫ e.hom =
      originalStageToCompatibleProj K n h m ≫ e'.hom) : e = e' := by
  apply Iso.ext
  exact completeFamilyHom_ext_stages K n h e.hom e'.hom hs

end FLT.Mazur.PolygonInfinitesimalStages
