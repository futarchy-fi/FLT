/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.KernelPairEffectiveOpenEtale
public import FLT.Mazur.KernelPairEtaleBranchImage

/-!
# Whole-source represented points from unrestricted etale branches

An etale branch of the original coefficient projection meeting the effective
region forces a point in its whole-source fppf region. On an irreducible target,
any nonempty such branch meets every nonempty effective region. Neither global
flatness nor global unramifiedness of the original projection is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.KernelPairEffectiveOpen
set_option backward.isDefEq.respectTransparency false
variable {D A T Z : Scheme.{u}} (p q : D ⟶ A) (w : A ⟶ T) (h : p ≫ w = q ≫ w)
  [Mono (pullback.lift p q h)] [Etale p] [LocallyOfFinitePresentation w]
local notation "U" => targetOpen p q w h
local notation "π" => projection p q w h

/-- A point of an unrestricted etale branch above the effective region yields a full fppf point. -/
theorem exists_fppf_point_of_etale_branch (a : Z ⟶ A) [Etale (a ≫ w)]
    (z : Z) (hz : (a ≫ w) z ∈ U) :
    ∃ y : source p q w h, π y ∈ SchemeFppfTargetOpen.locus π := by
  let B := pullback (a ≫ w) (U).ι
  let b : B ⟶ source p q w h :=
    pullback.lift (pullback.fst (a ≫ w) (U).ι ≫ a) (pullback.snd (a ≫ w) (U).ι)
      (by rw [Category.assoc]; exact pullback.condition)
  have hb : b ≫ π = pullback.snd (a ≫ w) (U).ι := pullback.lift_snd _ _ _
  let _ : Etale (b ≫ π) := by rw [hb]; infer_instance
  have hi := KernelPairEtaleGeometry.etale_branch_image_le_fppf
    (fst p q w h) (snd p q w h) π (isPullback p q w h) b
  obtain ⟨y, _, _⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback (a ≫ w) (U).ι) z ⟨(a ≫ w) z, hz⟩ rfl
  exact ⟨b y, hi ⟨y, rfl⟩⟩

/-- On an irreducible target, a nonempty unrestricted etale branch meets the effective open. -/
theorem fppfLocus_nonempty_of_etale_branch [IrreducibleSpace T]
    (a : Z ⟶ A) [Etale (a ≫ w)] [Nonempty Z]
    (hU : (U : Set T).Nonempty) :
    (SchemeFppfTargetOpen.locus π : Set (U).toScheme).Nonempty := by
  have hd : Dense (U : Set T) := (U).isOpen.dense hU
  obtain ⟨y, ⟨z, hz⟩, hy⟩ := hd.inter_open_nonempty
    (Set.range (a ≫ w)) (a ≫ w).isOpenMap.isOpen_range (Set.range_nonempty _)
  obtain ⟨x, hx⟩ := exists_fppf_point_of_etale_branch p q w h a z (by rwa [hz])
  exact ⟨π x, hx⟩

end FLT.Mazur.KernelPairEffectiveOpen
