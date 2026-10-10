/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeIndependentFamilyLineCategory
public import FLT.Mazur.SchemeFppfFamilyOverlapMapDetection

/-!
# Independent family assembly is fully faithful

The established source assembly equivalence supplies all source maps.
Detection of original pair equations makes their descent maps correspond
exactly to the maps between assembled geometric data.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeFppfFamily.IndependentLineData
open SchemeGeometricDescent
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] SchemeCoproductModuleGluing.assembled
variable {X : Scheme.{u}} {𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage X}

/-- The existing concrete source assembly is an equivalence by its member recovery. -/
lemma sourceAssembly_isEquivalence :
    (SchemeCoproductModuleGluing.assemble 𝒰.X).IsEquivalence := by
  let _ : (SchemeCoproductModuleGluing.assemble 𝒰.X ⋙
      SchemeCoproductModuleGluing.decompose 𝒰.X).IsEquivalence :=
    Functor.isEquivalence_of_iso (SchemeCoproductModuleGluing.memberRecovery 𝒰.X).symm
  exact Functor.isEquivalence_of_comp_right _ (SchemeCoproductModuleGluing.decompose 𝒰.X)

instance assemble_faithful : (assemble (𝒰 := 𝒰)).Faithful where
  map_injective h := by
    let _ := sourceAssembly_isEquivalence (𝒰 := 𝒰)
    apply hom_ext
    exact congrFun ((SchemeCoproductModuleGluing.assemble 𝒰.X).map_injective
      (congrArg Subtype.val h))

instance assemble_full : (assemble (𝒰 := 𝒰)).Full where
  map_surjective f := by
    let _ := sourceAssembly_isEquivalence (𝒰 := 𝒰)
    let g := (SchemeCoproductModuleGluing.assemble 𝒰.X).preimage f.val
    have hg : SchemeCoproductModuleGluing.map 𝒰.X g = f.val :=
      (SchemeCoproductModuleGluing.assemble 𝒰.X).map_preimage f.val
    have hc : PairMapCompatible 𝒰 _ _ g :=
      pairMapCompatible_of_assembled 𝒰 _ _ g (by rw [hg]; exact f.property)
    exact ⟨⟨g, hc⟩, LineData.hom_ext _ hg⟩

end FLT.Mazur.SchemeFppfFamily.IndependentLineData
