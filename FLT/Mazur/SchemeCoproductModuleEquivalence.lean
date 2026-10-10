/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeCoproductModuleGluing
public import FLT.Mazur.ModuleSheafOpenImmersionGluing
public import Mathlib.CategoryTheory.Pi.Basic

/-!
# Modules on a coproduct are independent families of modules

Pullback to the original members is fully faithful and essentially surjective.
The concrete assembly functor has the prescribed natural member recoveries.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeCoproductModuleGluing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {ι : Type u} (X : ι → Scheme.{u})

/-- Restrict a module on the coproduct to all its original components. -/
def decompose : (∐ X : Scheme).Modules ⥤ (∀ i, (X i).Modules) where
  obj M i := (pullback (Limits.Sigma.ι X i)).obj M
  map f i := (pullback (Limits.Sigma.ι X i)).map f

/-- The independent component modules assemble functorially. -/
def assemble : (∀ i, (X i).Modules) ⥤ (∐ X : Scheme).Modules where
  obj := assembled X
  map := map X
  map_id _ := map_id X
  map_comp f g := map_comp X f g

/-- The chosen assembly recovers every original component naturally. -/
def memberRecovery : assemble X ⋙ decompose X ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M ↦ Pi.isoMk (recovery X M)) (fun f ↦ by
    funext i
    exact map_recovery X f i)

/-- Every point belongs to an original coproduct component. -/
lemma jointly_covers (x : (∐ X : Scheme)) :
    ∃ i, x ∈ Set.range (Limits.Sigma.ι X i) := by
  have hx : x ∈ iSup (opens X) := by rw [covers]; trivial
  exact TopologicalSpace.Opens.mem_iSup.mp hx

/-- Arbitrary component pullback maps agree on all overlaps of the coproduct. -/
lemma pullbackMaps_compatible {M N : (∐ X : Scheme).Modules}
    (f : ∀ i, (pullback (Limits.Sigma.ι X i)).obj M ⟶
      (pullback (Limits.Sigma.ι X i)).obj N) :
    ModuleSheafOpenImmersionGluing.Compatible X (Limits.Sigma.ι X) f := by
  intro i j V hi hj
  by_cases hij : i = j
  · subst j; rfl
  · ext s
    exact @Subsingleton.elim Γ(N, V)
      (ModuleSheafEmptySlice.sections_subsingleton N V
        (ModuleSheafDisjointGluing.subopen_eq_bot (opens X) (disjoint X) hij V hi hj)) _ _

instance decompose_faithful : (decompose X).Faithful where
  map_injective h := ModuleSheafOpenImmersionGluing.hom_ext X (Limits.Sigma.ι X)
    (jointly_covers X) _ _ (congrFun h)

instance decompose_full : (decompose X).Full where
  map_surjective f := by
    obtain ⟨g, hg, _⟩ := ModuleSheafOpenImmersionGluing.existsUnique_glue X
      (Limits.Sigma.ι X) (jointly_covers X) f (pullbackMaps_compatible X f)
    exact ⟨g, funext hg⟩

instance decompose_essSurj : (decompose X).EssSurj where
  mem_essImage M := ⟨assembled X M, ⟨Pi.isoMk (recovery X M)⟩⟩

instance decompose_isEquivalence : (decompose X).IsEquivalence where

/-- The category of modules on a scheme coproduct is the category of independent families. -/
def moduleEquivalence : (∐ X : Scheme).Modules ≌ (∀ i, (X i).Modules) :=
  (decompose X).asEquivalence

end FLT.Mazur.SchemeCoproductModuleGluing
