/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedProjChartNaturality
public import FLT.Mazur.SectionGradedProjGeneratorChart
public import FLT.Mazur.ModuleSectionRatioPullback

/-!
# Pullback of invertible homogeneous section coordinates

An invertible homogeneous coordinate is an actual generator of its tensor
power. Generation persists after pullback, so the Proj maps restrict to
all overlaps without additional unit assumptions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.SectionGradedProjChart
open FCurve ModuleLineBundleTensorPullback SectionGradedSum SectionGradedCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y Z : Scheme} (p : Y ⟶ X) (L : X.Modules)
  (e : (pullback p).obj L ≅ structureModule Y)

/-- A generating pulled-back section has unit homogeneous coordinate. -/
lemma ringHom_isUnit_of_pullGenerator {d : ℕ} (s : Γ(tensorPower L d, ⊤))
    [IsIso (globalSectionHom _ (pullGlobal p (tensorPower L d) s))] :
    IsUnit (ringHom p L e (of L ⊤ d s)) := by
  have := globalSectionHom_isIso_transport _ (tensorPowerIso p L d)
    (pullGlobal p (tensorPower L d) s)
  rw [ringHom_of]
  change IsUnit (show Γ(Y, ⊤) from (tensorPowerTrivialization e d).hom.app ⊤
    ((tensorPowerIso p L d).hom.app ⊤ (pullGlobal p (tensorPower L d) s)))
  exact coordinate_isUnit_of_generator _ _ (tensorPowerTrivialization e d)

/-- A unit homogeneous coordinate certifies generation in the original pulled-back tensor power. -/
lemma pullGenerator_isIso_of_ringHom {d : ℕ} (s : Γ(tensorPower L d, ⊤))
    (hs : IsUnit (ringHom p L e (of L ⊤ d s))) :
    IsIso (globalSectionHom _ (pullGlobal p (tensorPower L d) s)) := by
  rw [ringHom_of] at hs
  have ht : IsIso (globalSectionHom (tensorPower ((pullback p).obj L) d)
      ((tensorPowerIso p L d).hom.app ⊤ (pullGlobal p (tensorPower L d) s))) :=
    globalSectionHom_isIso_of_coordinate _ _ (tensorPowerTrivialization e d) hs
  have : IsIso (globalSectionHom _ (pullGlobal p (tensorPower L d) s) ≫
      (tensorPowerIso p L d).hom) := by
    rw [globalSectionHom_naturality]
    exact ht
  exact IsIso.of_isIso_comp_right _ (tensorPowerIso p L d).hom

/-- Every further pullback retains an invertible homogeneous section coordinate. -/
lemma ringHom_isUnit_pullback (k : Z ⟶ Y)
    (e' : (pullback (k ≫ p)).obj L ≅ structureModule Z)
    {d : ℕ} (s : Γ(tensorPower L d, ⊤)) (hs : IsUnit (ringHom p L e (of L ⊤ d s))) :
    IsUnit (ringHom (k ≫ p) L e' (of L ⊤ d s)) := by
  have := pullGenerator_isIso_of_ringHom p L e s hs
  have := globalSectionHom_isIso_pullGlobal _ (pullGlobal p (tensorPower L d) s) k
  have := globalSectionHom_isIso_comp_pullGlobal k p (tensorPower L d) s
  exact ringHom_isUnit_of_pullGenerator (k ≫ p) L e' s

/-- The induced line trivialization on a further pullback. -/
def pullTrivialization (k : Z ⟶ Y) : (pullback (k ≫ p)).obj L ≅ structureModule Z :=
  ((pullbackComp k p).app L).symm ≪≫ (pullback k).mapIso e ≪≫ modulePullbackUnitIso k

variable [Fact (LocallyFreeRankOne L)]

/-- Equal structure morphisms and arbitrary line coordinates give equal local Proj maps. -/
lemma toProj_congr {q : Y ⟶ X} (hpq : p = q)
    (e' : (pullback q).obj L ≅ structureModule Y) (f : SectionGradedSum.Sections L ⊤)
    (hf : IsUnit (ringHom p L e f)) (hf' : IsUnit (ringHom q L e' f))
    {d : ℕ} (hd : f ∈ grade L ⊤ d) (hpos : 0 < d) :
    toProj p L e f hf hd hpos = toProj q L e' f hf' hd hpos := by
  subst q
  exact toProj_independent p L e e' f hf hf' hd hpos

/-- Naturality for a genuine homogeneous generator needs no additional unit-coordinate input. -/
lemma toProj_pullback (k : Z ⟶ Y) {d : ℕ} (s : Γ(tensorPower L d, ⊤))
    (hs : IsUnit (ringHom p L e (of L ⊤ d s))) (hd : 0 < d) :
    k ≫ toProj p L e (of L ⊤ d s) hs ⟨s, rfl⟩ hd =
      toProj (k ≫ p) L (pullTrivialization p L e k) (of L ⊤ d s)
        (ringHom_isUnit_pullback p L e k _ s hs) ⟨s, rfl⟩ hd :=
  toProj_naturality p L e k _ _ _ _ _ _

end FLT.Mazur.SectionGradedProjChart
