/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSectionLineRankOne
public import FLT.Mazur.FiniteFreeChartSectionLineComparison
public import FLT.Mazur.LineSubbundleGluing
public import FLT.Mazur.LocallySplitInclusionPullback

/-!
# Global assembly of compatible actual affine section lines

On any scheme, actual normalized lines in finite free affine charts glue
from equality of their overlap subobjects. The result is a line bundle
inside the original ambient module; every test pullback remains monic.
The input overlap condition is local and does not assume a global object.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.AffineSectionLineGluing
open AffineFreeSheafCoordinates FiniteFreeChartTransitions NormalizedSectionLine FCurve
variable {X : Scheme.{u}} {I : Type u} (U : I → X.Opens)
variable [∀ i, IsAffine (U i).toScheme] (M : X.Modules)
variable (ι : I → Type u) [∀ i, Finite (ι i)]
variable (e : ∀ i, M.restrict (U i).ι ≅ SheafOfModules.free (ι i))
variable (k : ∀ i, ι i) (L : ∀ i, Chart Γ((U i).toScheme, ⊤) (ι i) (k i))

/-- The local objects are the actual affine sheaves of the specified section submodules. -/
abbrev localLine (i : I) : (U i).toScheme.Modules :=
  sectionLineSheaf (U i).toScheme (k i) (L i)

/-- Their original free charts include the actual local lines in the ambient module. -/
abbrev localInclusion (i : I) : localLine U ι k L i ⟶ M.restrict (U i).ι :=
  chartSectionLineInclusion M le_rfl (e i) (k i) (L i)

/-- Compatibility asks only for equality of the two original subobjects on each overlap. -/
abbrev Compatible : Prop :=
  CoherentSubmoduleGluing.CompatibleInclusions U M (localLine U ι k L)
    (localInclusion U M ι e k L)

variable {U M ι e k L} (h : Compatible U M ι e k L) (hU : iSup U = ⊤)

/-- The globally assembled sheaf of actual compatible affine section lines. -/
abbrev line : X.Modules := LineSubbundleGluing.line h

/-- Its actual inclusion targets the original ambient module sheaf. -/
abbrev inclusion : line h ⟶ M := CoherentSubmoduleGluing.inclusion h hU

include hU in
/-- Local normalized coordinate projections prove global rank one of the constructed sheaf. -/
theorem rankOne : LocallyFreeRankOne (line h) :=
  LineSubbundleGluing.rankOne h hU
    (fun i ↦ sectionLineSheaf_rankOne (U i).toScheme (k i) (L i))

/-- Recover the prescribed sheaf of actual section submodules on each original affine chart. -/
def chartIso (i : I) : (line h).restrict (U i).ι ≅ localLine U ι k L i :=
  (CoherentSubmoduleGluing.data h).restrictionIso i

/-- Chart recovery preserves the original ambient inclusion. -/
lemma chartIso_inclusion (i : I) :
    (chartIso h i).hom ≫ localInclusion U M ι e k L i =
      (restrictFunctor (U i).ι).map (inclusion h hU) :=
  CoherentSubmoduleGluing.restriction_commutes h hU i

/-- The original local splittings imply monicity after any test-base change. -/
theorem pullback_mono {T : Scheme.{u}} (f : T ⟶ X) :
    Mono ((pullback f).map (inclusion h hU)) :=
  LocallySplitInclusionPullback.mono_of_split_cover (inclusion h hU) f U hU

include hU in
/-- The assembled line stays rank one over every test scheme. -/
theorem pullback_rankOne {T : Scheme.{u}} (f : T ⟶ X) :
    LocallyFreeRankOne ((pullback f).obj (line h)) := (rankOne h hU).pullback f

/-- The original local images characterize the global subobject uniquely. -/
theorem subobject_unique {N : X.Modules} (b : N ⟶ M) [Mono b]
    (hb : ∀ i, Subobject.mk ((restrictFunctor (U i).ι).map b) =
      Subobject.mk (localInclusion U M ι e k L i)) :
    Subobject.mk b = Subobject.mk (inclusion h hU) :=
  LineSubbundleGluing.subobject_unique h hU b hb

end FLT.Mazur.AffineSectionLineGluing
