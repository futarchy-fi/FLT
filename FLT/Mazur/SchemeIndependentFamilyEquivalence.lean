/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeIndependentCanonicalCompatibility
public import FLT.Mazur.SchemeIndependentFamilyAssemblyFullyFaithful

/-!
# Equivalence for independent fppf family line data

Every geometric family datum is effective. Canonical independent data of
its descended line bundle therefore supply a preimage for actual assembly.
The equivalences retain the previously constructed member recovery maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeFppfFamily.IndependentLineData
open SchemePicard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage X)

instance assemble_essSurj : (assemble (𝒰 := 𝒰)).EssSurj where
  mem_essImage D := by
    obtain ⟨L, ⟨e⟩⟩ := family_effective 𝒰 D
    exact ⟨canonicalObj 𝒰 L, ⟨(canonicalAssemblyIso 𝒰 L).symm ≪≫ e⟩⟩

instance assemble_isEquivalence : (assemble (𝒰 := 𝒰)).IsEquivalence where

/-- Actual assembly is an equivalence from original independent data to geometric data. -/
def assemblyEquivalence : IndependentLineData 𝒰 ≌ FamilyLineData 𝒰 :=
  (assemble (𝒰 := 𝒰)).asEquivalence

/-- Independent member data descend equivalently to line bundles on the base. -/
def baseEquivalence : IndependentLineData 𝒰 ≌ LineBundleCat X :=
  (assemblyEquivalence 𝒰).trans (familyLineEquivalence 𝒰).symm

/-- The equivalence uses the already constructed effective descent functor. -/
lemma baseEquivalence_functor : (baseEquivalence 𝒰).functor = descend := rfl

/-- The assembly equivalence retains the original natural member recovery. -/
def assemblyEquivalenceMemberRecovery (i : 𝒰.I₀) :
    (assemblyEquivalence 𝒰).functor ⋙ component 𝒰 i ≅
      members ⋙ (Pi.eval _ i) ⋙ lineBundleForget (𝒰.X i) :=
  assemblyMemberRecovery i

/-- The base equivalence retains the original effective member recovery naturally. -/
def baseEquivalenceMemberRecovery (i : 𝒰.I₀) :
    (baseEquivalence 𝒰).functor ⋙ lineBundleForget X ⋙ pullback (𝒰.f i) ≅
      members ⋙ (Pi.eval _ i) ⋙ lineBundleForget (𝒰.X i) :=
  descentMemberRecovery i

/-- The retained natural recovery is precisely the constructed recovery of each member. -/
lemma baseEquivalenceMemberRecovery_app (D : IndependentLineData 𝒰) (i : 𝒰.I₀) :
    (baseEquivalenceMemberRecovery 𝒰 i).app D = D.descendedMemberRecovery i := rfl

end FLT.Mazur.SchemeFppfFamily.IndependentLineData
