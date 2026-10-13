/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFppfRepresentedCover

/-!
# Detecting geometric surjectivity on the relative fppf site

Local lifts of the identity give a jointly surjective family of actual scheme
maps factoring through the given morphism. No flatness hypothesis is needed
for this direction.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.RelativeFppfRepresentedCover
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {S : Scheme.{u}} {U Z : Over S} (a : U ⟶ Z)

/-- Local surjectivity on the original relative site detects geometric surjectivity. -/
theorem surjective_of_isLocallySurjective
    [Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (uliftYoneda.{u + 1}.map a)] :
    Surjective a.left := by
  have h : Presheaf.imageSieve (uliftYoneda.{u + 1}.map a) (ULift.up (𝟙 Z)) ∈
      (Scheme.fppfTopology.over S) Z := Presheaf.IsLocallySurjective.imageSieve_mem _
  rw [GrothendieckTopology.mem_over_iff] at h
  let _ : Scheme.fppfPrecoverage.{u}.HasIsos :=
    ⟨fun g _ ↦ g.singleton_mem_fppfPrecoverage⟩
  obtain ⟨Q, hQ, hle⟩ :=
    Scheme.fppfPrecoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mp h
  have hsurj := (Presieve.mem_comap_jointlySurjectivePrecoverage_iff Scheme.forget).mp hQ.1
  refine ⟨fun z ↦ ?_⟩
  obtain ⟨W, g, hg, w, hw⟩ := hsurj z
  have hg' := (Sieve.overEquiv_iff _ _).mp (hle _ _ hg)
  obtain ⟨v, hv⟩ := hg'
  have he : v.down.left ≫ a.left = g := by
    have he' := congrArg ULift.down hv
    change v.down ≫ a = Over.homMk g ≫ 𝟙 Z at he'
    simpa only [Category.comp_id, Over.comp_left, Over.homMk_left] using
      congrArg Over.Hom.left he'
  exact ⟨v.down.left w, (congrArg (fun k : W ⟶ Z.left ↦ k w) he).trans hw⟩

/-- A represented epimorphism in relative fppf sheaves is geometrically surjective. -/
theorem surjective_of_sheaf_epi
    [Epi ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map a)] : Surjective a.left := by
  let _ : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (uliftYoneda.{u + 1}.map a) := (Sheaf.isLocallySurjective_iff_epi
    ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map a)).mpr inferInstance
  exact surjective_of_isLocallySurjective a

end FLT.Mazur.RelativeFppfRepresentedCover
