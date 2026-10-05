/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSectionTwistSystem
public import FLT.Mazur.AmpleAffinePullback
public import FLT.Mazur.PrincipalSectionExtension
public import FLT.Mazur.ModuleOpenCohomologyRestriction
public import FLT.Mazur.GlobalIdealPower
public import FLT.Mazur.AffineCohomologyVanishingAffine

/-!
# Ideal-twist cohomology and restriction

Apply genuine module cohomology to the section-multiplication system and to
its restriction. The restriction maps form a natural transformation. On an
affine generator open the positive-degree target is zero; this alone does
not assert that a class is killed at a finite stage of the global system.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxSynthPendingDepth 1

namespace FLT.Mazur.FCurve

local instance twistRestrictionHasExt (T : TopCat.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) :=
  HasExt.standard _

set_option maxHeartbeats 800000 in
-- Comparing the two Ext presentations unfolds the open-restriction equivalence.
/-- Restriction in module cohomology commutes with arbitrary coefficient maps. -/
lemma moduleGlobalRestriction_naturality {X : Scheme.{u}} (W : X.Opens)
    {M N : X.Modules} (a : M ⟶ N) (q : ℕ) (x : ModuleH M q) :
    moduleGlobalRestriction W N q (moduleHMap a q x) =
      moduleHMap ((restrictFunctor W.ι).map a) q (moduleGlobalRestriction W M q x) :=
  OpenSheafCohomologyRestriction.globalOpenRestriction_naturality W
    ((SheafOfModules.toSheaf X.ringCatSheaf).map a) q x

namespace LineSectionTwistSystem

open ModuleSheafTensor ModuleLineBundleTensorPullback

variable {k : Type} [Field k] {X : Scheme}
  (f : X ⟶ Spec (CommRingCat.of k)) (M : X.Modules) {L : X.Modules} (s : Γ(L, ⊤))

/-- The cohomology system retains its actual sheaf coefficients and field action. -/
def cohomology (q : ℕ) : ℕ ⥤ ModuleCat.{1} k :=
  system M s ⋙ moduleScalarHFunctor f q

/-- The same system restricted to a specified open before taking cohomology. -/
def openCohomology (W : X.Opens) (q : ℕ) : ℕ ⥤ ModuleCat.{1} k :=
  system M s ⋙ restrictFunctor W.ι ⋙ moduleScalarHFunctor (W.ι ≫ f) q

/-- Global-to-open restriction is linear for the common base field. -/
def restrictLinear (W : X.Opens) (N : X.Modules) (q : ℕ) :
    ModuleScalarH f N q →ₗ[k] ModuleScalarH (W.ι ≫ f) (N.restrict W.ι) q where
  toAddHom := (moduleGlobalRestriction W N q).toAddHom
  map_smul' a x := by
    change ModuleH N q at x
    change moduleGlobalRestriction W N q (structureScalarMap f a • x) =
      structureScalarMap (W.ι ≫ f) a • moduleGlobalRestriction W N q x
    rw [globalOpenRestriction_smul]
    rfl

/-- A natural transformation of directed systems, not just unrelated restrictions. -/
def restriction (W : X.Opens) (q : ℕ) :
    cohomology f M s q ⟶ openCohomology f M s W q where
  app n := ModuleCat.ofHom (restrictLinear f W ((system M s).obj n) q)
  naturality {i j} a := by
    ext x
    exact moduleGlobalRestriction_naturality W ((system M s).map a) q x

@[simp]
lemma cohomology_map_succ (q n : ℕ) :
    (cohomology f M s q).map (homOfLE (Nat.le_add_right n 1)) =
      ModuleCat.ofHom (moduleScalarHMap f (step M s n) q) := by
  change (moduleScalarHFunctor f q).map
    ((system M s).map (homOfLE (Nat.le_add_right n 1))) = _
  rw [system_map_succ]
  rfl

/-- Restricted successor maps are isomorphisms in every cohomological degree. -/
theorem openCohomology_map_succ_isIso (q n : ℕ) :
    IsIso ((openCohomology f M s (sectionGeneratorOpen L s) q).map
      (homOfLE (Nat.le_add_right n 1))) := by
  change IsIso ((moduleScalarHFunctor ((sectionGeneratorOpen L s).ι ≫ f) q).map
    ((restrictFunctor (sectionGeneratorOpen L s).ι).map
      ((system M s).map (homOfLE (Nat.le_add_right n 1)))))
  rw [system_map_succ]
  have := step_isIso_on_generatorOpen M s n
  infer_instance

/-- Affine restriction kills positive cohomology at each stage of any coherent twist system. -/
theorem restriction_eq_zero [IsLocallyNoetherian X] [M.IsFinitePresentation]
    (hL : LocallyFreeRankOne L) (W : X.Opens) (hW : IsAffineOpen W)
    (q : ℕ) (hq : 0 < q) : restriction f M s W q = 0 := by
  have : IsAffine W.toScheme := hW
  ext n x
  have := (hL.tensorPower n).isFinitePresentation
  have := FLT.Mazur.GlobalIdealPower.tensor_coherent M (tensorPower L n)
  exact affine_moduleH_eq_zero
    ((tensor M (tensorPower L n)).restrict W.ι) q hq _

/-- Specialization to arbitrary ideal coefficients, with no invertibility condition on the ideal. -/
def idealCohomology (I : X.IdealSheafData) (q : ℕ) : ℕ ⥤ ModuleCat.{1} k :=
  cohomology f (idealModule I) s q

/-- The ideal-twist H¹ restriction vanishes on an affine generator open. -/
theorem idealHOne_restriction_eq_zero [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hL : LocallyFreeRankOne L)
    (hs : IsAffineOpen (sectionGeneratorOpen L s)) :
    restriction f (idealModule I) s (sectionGeneratorOpen L s) 1 = 0 := by
  have := FLT.Mazur.CoherentIdealIntersection.idealModule_coherent I
  exact restriction_eq_zero f (idealModule I) s hL _ hs 1 (by decide)

end LineSectionTwistSystem
end FLT.Mazur.FCurve
