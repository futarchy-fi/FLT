/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSectionGenericOpen
public import FLT.Mazur.SectionGeneratorSpan
public import FLT.Mazur.LineBundleSectionOpenPullback
public import FLT.Mazur.SmoothFiniteSubschemeCartier
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# A genuine point condition detected by a nonzero line section

Over an algebraically closed field, a nonzero section on a reduced finite-type
scheme generates at a rational closed point. Its actual scheme-theoretic image
ideal has quotient isomorphic to the base field. On a smooth curve that ideal
is Cartier, and the original section remains nonzero on its closed subscheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

variable {k : Type} [Field k] [IsAlgClosed k] {X : Scheme}
  (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]

/-- A nonzero line section generates at an actual rational point. -/
theorem exists_rational_point_generating_section [IsReduced X]
    {L : X.Modules} (hL : LocallyFreeRankOne L) (s : Γ(L, ⊤)) (hs : s ≠ 0) :
    ∃ p : Spec (.of k) ⟶ X, p ≫ f = 𝟙 _ ∧
      p (IsLocalRing.closedPoint k) ∈ sectionGeneratorOpen L s := by
  let _ : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, hx, hc⟩ := nonempty_inter_closedPoints
    (sectionGeneratorOpen_nonempty hL s hs) (sectionGeneratorOpen L s).isOpen.isLocallyClosed
  exact ⟨pointOfClosedPoint f x hc, pointOfClosedPoint_comp f x hc,
    (pointOfClosedPoint_apply f x hc _).symm ▸ hx⟩

omit [IsAlgClosed k] [LocallyOfFiniteType f] in
/-- The full image subscheme of a rational section is isomorphic to the base. -/
theorem rational_point_image_isIso (p : Spec (.of k) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    IsIso (p.ker.subschemeι ≫ f) := by
  let _ : IsClosedImmersion p := isClosedImmersion_of_comp_eq_id f p hp
  have : IsIso (p.toImage ≫ (p.ker.subschemeι ≫ f)) := by
    rw [← Category.assoc, p.toImage_imageι, hp]
    infer_instance
  exact IsIso.of_isIso_comp_left p.toImage (p.ker.subschemeι ≫ f)

/-- Point subtraction uses a full Cartier ideal and a nonzero original restriction. -/
theorem exists_cartier_point_condition [IsReduced X] [SmoothOfRelativeDimension 1 f]
    {L : X.Modules} (hL : LocallyFreeRankOne L) (s : Γ(L, ⊤)) (hs : s ≠ 0) :
    ∃ I : X.IdealSheafData, EffectiveCartier I ∧ IsIso (I.subschemeι ≫ f) ∧
      pullGlobal I.subschemeι L s ≠ 0 := by
  obtain ⟨p, hp, hg⟩ := exists_rational_point_generating_section f hL s hs
  let _ : IsClosedImmersion p := isClosedImmersion_of_comp_eq_id f p hp
  let _ := rational_point_image_isIso f p hp
  refine ⟨p.ker, effectiveCartier_of_smoothCurve_finite f p.ker, inferInstance, ?_⟩
  intro hz
  let z := p.toImage (IsLocalRing.closedPoint k)
  have hm : z ∈ sectionGeneratorOpen ((pullback p.ker.subschemeι).obj L)
      (pullGlobal p.ker.subschemeι L s) := by
    rw [sectionGeneratorOpen_pullGlobal hL]
    have he : p.ker.subschemeι z = p (IsLocalRing.closedPoint k) := rfl
    exact (show p.ker.subschemeι z ∈ sectionGeneratorOpen L s from he.symm ▸ hg)
  rw [hz, sectionGeneratorOpen_zero] at hm
  exact hm

end FLT.Mazur.FCurve
