/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentIdealIntersection
public import FLT.Mazur.IdealQuotientExact

/-!
# The quotient of two comaximal ideal sheaves

The actual maps give the sequence I ∩ J → I → O/J. The intersection is its
kernel on every scheme; comaximality makes the last map surjective on affine
sections, hence gives a short exact sequence of module sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules FLT.Mazur.ModuleSubobjectCoverEquality
open FLT.Mazur.ModuleSheafMorphismGluing

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace FLT.Mazur.CoherentIdealIntersection

open FCurve

variable {X : Scheme.{u}} (I J : X.IdealSheafData)

/-- The ideal inclusion followed by reduction modulo the second ideal. -/
def reduction : idealModule I ⟶ (pushforward J.subschemeι).obj
    (structureModule J.subscheme) := idealModuleι I ≫ idealQuotientMap J

/-- The intersection inclusion is killed by reduction. -/
lemma intersection_reduction :
    idealMap (inf_le_left : I ⊓ J ≤ I) ≫ reduction I J = 0 := by
  rw [reduction, ← Category.assoc, idealMap_comp,
    ← idealMap_comp (inf_le_right : I ⊓ J ≤ J), Category.assoc]
  exact (by rw [show idealModuleι J ≫ idealQuotientMap J = 0 from kernel.condition _,
    comp_zero])

/-- The actual intersection and quotient maps form a short complex. -/
def reductionComplex : ShortComplex X.Modules :=
  ShortComplex.mk _ _ (intersection_reduction I J)

/-- A morphism killed modulo J factors through the intersection. -/
def intersectionLift {M : X.Modules} (a : M ⟶ idealModule I)
    (ha : a ≫ reduction I J = 0) : M ⟶ idealModule (I ⊓ J) :=
  factor (a ≫ idealModuleι I) (idealModuleι (I ⊓ J)) (by
    apply sections_of_local
    intro V s x hx
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
    refine ⟨U, hUV, hxU, ?_⟩
    rw [← Set.mem_range, idealModuleι_range (I ⊓ J) ⟨U, hU⟩]
    refine ⟨?_, ?_⟩
    · exact (Set.ext_iff.mp (idealModuleι_range I ⟨U, hU⟩) _).mp ⟨_, rfl⟩
    · rw [← idealQuotientMap_ker J ⟨U, hU⟩]
      exact congrArg (fun f ↦ f.app U (res M hUV s)) ha)

@[reassoc (attr := simp)]
lemma intersectionLift_inclusion {M : X.Modules} (a : M ⟶ idealModule I)
    (ha : a ≫ reduction I J = 0) :
    intersectionLift I J a ha ≫ idealMap (inf_le_left : I ⊓ J ≤ I) = a := by
  apply (cancel_mono (idealModuleι I)).mp
  rw [Category.assoc, idealMap_comp]
  exact factor_comp _ _ _

/-- The intersection realizes the categorical kernel of the reduction map. -/
def intersectionKernel : IsLimit (KernelFork.ofι
    (idealMap (inf_le_left : I ⊓ J ≤ I)) (intersection_reduction I J)) :=
  KernelFork.IsLimit.ofι _ _ (fun a ha ↦ intersectionLift I J a ha)
    (fun a ha ↦ intersectionLift_inclusion I J a ha)
    (fun a ha _m hm ↦ (cancel_mono (idealMap (inf_le_left : I ⊓ J ≤ I))).mp
      (hm.trans (intersectionLift_inclusion I J a ha).symm))

/-- Reduction from I is surjective on affine sections when I and J are comaximal. -/
theorem reduction_affine_surjective (h : I ⊔ J = ⊤) (U : X.affineOpens) :
    Function.Surjective ((reduction I J).app U.1) := by
  intro s
  obtain ⟨r, rfl⟩ := idealQuotientMap_affine_surjective J U s
  have hr : r ∈ I.ideal U ⊔ J.ideal U := by
    change r ∈ (I ⊔ J).ideal U
    rw [h]
    trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hr
  obtain ⟨t, ht⟩ := (Set.ext_iff.mp (idealModuleι_range I U) a).mpr ha
  refine ⟨t, ?_⟩
  change (idealQuotientMap J).app U.1 ((idealModuleι I).app U.1 t) = _
  rw [ht, ← hab, map_add]
  have hb' : (idealQuotientMap J).app U.1 b = 0 := by
    exact (show b ∈ ((idealQuotientMap J).val.app (op U.1)).hom.ker from
      (idealQuotientMap_ker J U).symm ▸ hb)
  rw [hb', add_zero]

/-- Comaximality makes the actual reduction map an epimorphism. -/
theorem reduction_epi (h : I ⊔ J = ⊤) : Epi (reduction I J) where
  left_cancellation g k he := by
    apply moduleHom_ext_affine
    intro U
    ext s
    obtain ⟨t, rfl⟩ := reduction_affine_surjective I J h U s
    exact congrArg (fun f ↦ f.app U.1 t) he

/-- The comaximal ideal sequence is short exact. -/
theorem reductionComplex_shortExact (h : I ⊔ J = ⊤) :
    (reductionComplex I J).ShortExact := by
  have := reduction_epi I J h
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel _ (intersectionKernel I J))
    (inferInstanceAs (Mono (idealMap (inf_le_left : I ⊓ J ≤ I))))
    (reduction_epi I J h)

end FLT.Mazur.CoherentIdealIntersection
