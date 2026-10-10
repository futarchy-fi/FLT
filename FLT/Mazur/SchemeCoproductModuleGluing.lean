/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafDisjointGluing
public import FLT.Mazur.ModuleSheafOpenImageMapRecovery
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Assembling independent modules on a scheme coproduct

Arbitrary modules on the components glue on their disjoint image opens.
The recovery isomorphisms use the actual coproduct inclusions and retain maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeCoproductModuleGluing
open ModuleSheafOpenImageChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] ModuleSheafDisjointGluing.glued
variable {ι : Type u} (X : ι → Scheme.{u})

/-- The image opens of the actual coproduct inclusions. -/
abbrev opens (i : ι) : (∐ X : Scheme).Opens := (Limits.Sigma.ι X i).opensRange

/-- Distinct coproduct components have disjoint image opens. -/
lemma disjoint : Pairwise (fun i j ↦ Disjoint (opens X i) (opens X j)) :=
  fun i j h ↦ disjoint_opensRange_sigmaι X i j h

/-- The coproduct image opens cover the entire coproduct. -/
lemma covers : iSup (opens X) = ⊤ := (sigmaOpenCover X).iSup_opensRange

variable (M : ∀ i, (X i).Modules)

/-- Transport the independently supplied modules to the image opens. -/
abbrev imageModules (i : ι) := imageModule (Limits.Sigma.ι X i) (M i)

/-- The actual module sheaf assembled on the scheme coproduct. -/
def assembled : (∐ X : Scheme).Modules :=
  ModuleSheafDisjointGluing.glued (opens X) (disjoint X) (imageModules X M)

/-- Assembly recovers the supplied module on its image open. -/
def imageRecovery (i : ι) :
    (assembled X M).restrict (opens X i).ι ≅ imageModules X M i :=
  ModuleSheafDisjointGluing.recovery (opens X) (disjoint X) (imageModules X M) i

/-- Actual pullback along the original coproduct inclusion recovers its module. -/
def recovery (i : ι) : (pullback (Limits.Sigma.ι X i)).obj (assembled X M) ≅ M i :=
  pullbackRecovery (Limits.Sigma.ι X i) (M i) (assembled X M) (imageRecovery X M i)

variable {M} {N : ∀ i, (X i).Modules}

/-- Assemble independently supplied component maps. -/
def map (f : ∀ i, M i ⟶ N i) : assembled X M ⟶ assembled X N :=
  ModuleSheafDisjointGluing.map (opens X) (disjoint X) (covers X)
    (fun i ↦ imageMap (Limits.Sigma.ι X i) (f i))

/-- Recovery preserves each original component map. -/
lemma map_recovery (f : ∀ i, M i ⟶ N i) (i : ι) :
    (pullback (Limits.Sigma.ι X i)).map (map X f) ≫ (recovery X N i).hom =
      (recovery X M i).hom ≫ f i :=
  pullbackRecovery_naturality (Limits.Sigma.ι X i) (imageRecovery X M i)
    (imageRecovery X N i) (f i) (map X f)
    (ModuleSheafDisjointGluing.map_recovery (opens X) (disjoint X) (covers X) _ i)

@[simp]
lemma map_id : map X (fun i ↦ 𝟙 (M i)) = 𝟙 (assembled X M) := by
  have h : (fun i ↦ imageMap (Limits.Sigma.ι X i) (𝟙 (M i))) =
      (fun i ↦ 𝟙 (imageModules X M i)) := by
    funext i
    exact (pushforward (imageIso (Limits.Sigma.ι X i)).hom).map_id (M i)
  unfold map
  rw [h]
  exact ModuleSheafDisjointGluing.map_id (opens X) (disjoint X) (covers X)

@[simp]
lemma map_comp {P : ∀ i, (X i).Modules} (f : ∀ i, M i ⟶ N i)
    (g : ∀ i, N i ⟶ P i) : map X (fun i ↦ f i ≫ g i) = map X f ≫ map X g := by
  simp only [map, imageMap, Functor.map_comp, ModuleSheafDisjointGluing.map_comp]

end FLT.Mazur.SchemeCoproductModuleGluing
