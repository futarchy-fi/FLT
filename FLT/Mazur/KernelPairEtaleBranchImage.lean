/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.KernelPairEtaleUnramified
public import FLT.Mazur.SchemeFppfTargetOpen
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-!
# Covering the whole source above an etale branch image

For a full etale kernel relation, any etale target neighborhood lifting to
the source propagates flatness to the complete source above its image. The
original projection need not be flat away from this constructed image.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.KernelPairEtaleGeometry
set_option backward.isDefEq.respectTransparency false
variable {D A T Z : Scheme.{u}} (p q : D ⟶ A) (w : A ⟶ T)
  (H : IsPullback p q w w) [Etale p] (a : Z ⟶ A)
include H

/-- A lifted target test has an etale whole-source pullback, even if the test is nonreduced. -/
theorem branch_pullback_etale : Etale (pullback.snd w (a ≫ w)) := by
  have B := (IsPullback.of_hasPullback p a).paste_horiz H.flip
  rw [← B.isoPullback_inv_snd]
  infer_instance

/-- Every etale lifted target image lies in the maximal whole-source fppf target open. -/
theorem etale_branch_image_le_fppf [LocallyOfFinitePresentation w] [Etale (a ≫ w)] :
    Set.range (a ≫ w) ⊆ (SchemeFppfTargetOpen.locus w : Set T) := by
  let t := a ≫ w
  let U : T.Opens := ⟨Set.range t, t.isOpenMap.isOpen_range⟩
  let t' : Z ⟶ U.toScheme := IsOpenImmersion.lift U.ι t (by simp [U])
  have ht : t' ≫ U.ι = t := IsOpenImmersion.lift_fac _ _ _
  let _ : Etale (t' ≫ U.ι) := by rw [ht]; infer_instance
  let _ : Etale t' := Etale.of_comp t' U.ι
  let _ : Surjective t' := ⟨by
    rintro ⟨x, z, hz⟩
    refine ⟨z, ?_⟩
    apply U.ι.injective
    exact (congrArg (fun g ↦ g z) ht).trans hz⟩
  let v := pullback.snd w U.ι
  have B := (IsPullback.of_hasPullback v t').paste_horiz
    (IsPullback.of_hasPullback w U.ι)
  rw [ht] at B
  let _ : Etale (pullback.snd w t) := branch_pullback_etale p q w H a
  let _ : Etale (pullback.snd v t') := by
    rw [← B.isoPullback_hom_snd]
    infer_instance
  have hv : Etale v := MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Etale) (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
    (f := v) (g := t') ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  let _ := hv
  apply (SchemeFppfTargetOpen.le_locus_iff w U).mpr
  refine ⟨inferInstance, ⟨fun y ↦ ?_⟩⟩
  have hy : y ∈ Set.range (pullback.snd w U.ι) := by
    rw [Scheme.Pullback.range_snd]
    obtain ⟨z, hz⟩ := y.property
    exact ⟨a z, hz⟩
  exact hy

end FLT.Mazur.KernelPairEtaleGeometry
