/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedBaseChangeAlgebra

/-!
# Homogeneous pieces under section-algebra base change

The algebra comparison carries the scalar extension of each actual degree
onto the corresponding degree in the pulled-back section ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open scoped DirectSum ChangeOfRings
namespace FLT.Mazur.SectionGradedBaseChange
open FCurve ModuleLineBundleTensorPullback OpenModuleSectionScalars
open LinePowerSectionBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P X T S : Scheme}

/-- The homogeneous inclusion with the original structural base scalars. -/
abbrev baseOf (f : X ⟶ S) (L : X.Modules) (n : ℕ) :
    openSections f (tensorPower L n) ⊤ →ₗ[Γ(S, ⊤)] sectionModule f L :=
  DirectSum.lof Γ(S, ⊤) ℕ (fun n ↦ openSections f (tensorPower L n) ⊤) n

/-- A homogeneous piece of the section ring, over the structural base. -/
def baseGrade (f : X ⟶ S) (L : X.Modules) (n : ℕ) :
    Submodule Γ(S, ⊤) (sectionModule f L) := LinearMap.range (baseOf f L n)

/-- The scalar extension of the actual homogeneous inclusion. -/
def extendedOf (f : X ⟶ S) (L : X.Modules) (g : T ⟶ S) (n : ℕ) :
    (ModuleCat.extendScalars g.appTop.hom).obj (openSections f (tensorPower L n) ⊤) →ₗ[Γ(T, ⊤)]
      (ModuleCat.extendScalars g.appTop.hom).obj (sectionModule f L) :=
  ((ModuleCat.extendScalars g.appTop.hom).map (ModuleCat.ofHom (baseOf f L n))).hom

/-- The extended homogeneous piece is the range of the extended inclusion. -/
def extendedGrade (f : X ⟶ S) (L : X.Modules) (g : T ⟶ S) (n : ℕ) :
    Submodule Γ(T, ⊤) ((ModuleCat.extendScalars g.appTop.hom).obj (sectionModule f L)) :=
  LinearMap.range (extendedOf f L g n)

variable [CompactSpace X] [X.IsSeparated] [IsAffine T] [IsAffine S]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S} [Flat g]
  (h : IsPullback p q f g) (L : X.Modules) (hL : LocallyFreeRankOne L)

/-- The full comparison intertwines the actual extended degree inclusions. -/
lemma sectionsIso_extendedOf (n : ℕ)
    (s : (ModuleCat.extendScalars g.appTop.hom).obj (openSections f (tensorPower L n) ⊤)) :
    (sectionsIso h L hL).hom (extendedOf f L g n s) =
      baseOf q ((pullback p).obj L) n ((degreeIso h L hL n).hom s) := by
  induction s using TensorProduct.inductionOn with
  | tmul b s =>
    change (sectionsIso h L hL).hom
      (b ⊗ₜ[Γ(S, ⊤),g.appTop.hom] baseOf f L n s) = _
    exact sectionsIso_tmul_of h L hL n b s
  | add s t hs ht => simp only [map_add, hs, ht]

/-- The algebra equivalence maps each extended homogeneous piece onto its target piece. -/
lemma sectionsAlgEquiv_map_grade (n : ℕ) :
    Submodule.map (sectionsAlgEquiv h L hL).toLinearMap (extendedGrade f L g n) =
      baseGrade q ((pullback p).obj L) n := by
  ext y
  constructor
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    exact ⟨(degreeIso h L hL n).hom s, (sectionsIso_extendedOf h L hL n s).symm⟩
  · rintro ⟨s, rfl⟩
    refine ⟨extendedOf f L g n ((degreeIso h L hL n).inv s), ⟨_, rfl⟩, ?_⟩
    change (sectionsIso h L hL).hom _ = _
    rw [sectionsIso_extendedOf]
    congr 1
    exact ConcreteCategory.congr_hom (degreeIso h L hL n).inv_hom_id s

/-- Homogeneity is reflected as well as preserved by the full algebra equivalence. -/
lemma sectionsAlgEquiv_mem_grade_iff (n : ℕ)
    (s : (ModuleCat.extendScalars g.appTop.hom).obj (sectionModule f L)) :
    sectionsAlgEquiv h L hL s ∈ baseGrade q ((pullback p).obj L) n ↔
      s ∈ extendedGrade f L g n := by
  rw [← sectionsAlgEquiv_map_grade h L hL n]
  constructor
  · rintro ⟨t, ht, he⟩
    have : t = s := (sectionsAlgEquiv h L hL).injective he
    exact this ▸ ht
  · intro hs
    exact ⟨s, hs, rfl⟩

end FLT.Mazur.SectionGradedBaseChange
