/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VeryAmpleAffineSections

/-!
# Closed-presentation ampleness implies section ampleness

Positive powers with closed projective presentations supply affine generator
opens on every affine base restriction. This proves the forward comparison
without assuming any projective-immersion criterion in the converse direction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
variable {X S : Scheme} {f : X ⟶ S} {L : X.Modules}

/-- The closed-presentation predicate implies ordinary relative section ampleness. -/
theorem RelativeAmple.relativelyAmpleLineBundle (h : RelativeAmple f L)
    (hL : LocallyFreeRankOne L) : RelativelyAmpleLineBundle f L := by
  let := h.isProper
  refine ⟨inferInstance, hL, fun U hU ↦ ?_⟩
  obtain ⟨m, hm, ⟨p⟩⟩ := h U hU
  let e := tensorPowerRestrictIso L (f ⁻¹ᵁ U).ι m
  have hcompact : CompactSpace (f ⁻¹ᵁ U).toScheme := by
    let : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU.isCompact
    exact QuasiCompact.compactSpace_of_compactSpace (f ∣_ U)
  refine ⟨hcompact, hL.restrict _, fun x ↦ ?_⟩
  obtain ⟨s, hx, hs⟩ := p.exists_affine_generator_section x
  refine ⟨m, hm, e.hom.app ⊤ s, ?_, ?_⟩
  · simpa only [sectionGeneratorOpen_iso] using hx
  · simpa only [sectionGeneratorOpen_iso] using hs

end FLT.Mazur.FCurve
