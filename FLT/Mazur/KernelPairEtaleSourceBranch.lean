/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MonomorphismFiniteEtaleInverse

/-!
# Original kernel inverses from etale source branches

A branch etale over both the original source and the coefficient target
constructs inverse neighborhoods at every original relation arrow whose
second endpoint it meets. No geometry of the unrestricted projection is
assumed. All pullbacks retain their full scheme structure.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.KernelPairEtaleSourceBranch
set_option backward.isDefEq.respectTransparency false
variable {D A T Z : Scheme.{u}} (p q : D ⟶ A) (w : A ⟶ T)
  (h : p ≫ w = q ≫ w) (a : Z ⟶ A) [Etale p] [Etale a] [Etale (a ≫ w)]
local notation "m" => pullback.lift p q h

/-- Restricting an endpoint to a two-sided etale branch makes the comparison etale. -/
theorem comparison_etale : Etale (pullback.fst q a ≫ m) := by
  let j := pullback.fst (pullback.snd w w) a
  have H := (IsPullback.of_hasPullback (pullback.snd w w) a).paste_horiz
    (IsPullback.of_hasPullback w w)
  let _ : Etale (j ≫ pullback.fst w w) :=
    MorphismProperty.of_isPullback H.flip (inferInstanceAs (Etale (a ≫ w)))
  let b : pullback q a ⟶ pullback (pullback.snd w w) a :=
    pullback.lift (pullback.fst q a ≫ m) (pullback.snd q a)
      (by rw [Category.assoc, pullback.lift_snd]; exact pullback.condition)
  have hb : b ≫ j = pullback.fst q a ≫ m := pullback.lift_fst _ _ _
  let _ : Etale (b ≫ (j ≫ pullback.fst w w)) := by
    rw [← Category.assoc, hb, Category.assoc, pullback.lift_fst]
    infer_instance
  let _ : Etale b := Etale.of_comp b (j ≫ pullback.fst w w)
  rw [← hb]
  infer_instance

variable [Mono (pullback.lift p q h)]

/-- Actual relation points over the branch acquire inverse neighborhoods in the full kernel. -/
theorem mem_inverse_of_endpoint (r : D) (hr : q r ∈ Set.range a) :
    m r ∈ MonomorphismOpenImage.locus m := by
  obtain ⟨z, hz⟩ := hr
  obtain ⟨s, hs, _⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback q a) r z hz.symm
  let _ := comparison_etale p q w h a
  have he := MonomorphismOpenImage.mem_locus_of_fppf_lift m
    (pullback.fst q a ≫ m) (pullback.fst q a) rfl s
  change m (pullback.fst q a s) ∈ _ at he
  rwa [hs] at he

/-- Point coverage suffices on the kernel strip whose second endpoint meets the branch. -/
theorem mem_inverse_of_image (x : (pullback w w : Scheme))
    (hx : x ∈ Set.range m) (ha : pullback.snd w w x ∈ Set.range a) :
    x ∈ MonomorphismOpenImage.locus m := by
  obtain ⟨r, rfl⟩ := hx
  apply mem_inverse_of_endpoint p q w h a r
  simpa only [← Scheme.Hom.comp_apply, pullback.lift_snd] using ha

end FLT.Mazur.KernelPairEtaleSourceBranch
