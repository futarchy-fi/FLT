/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentSubmoduleGluing
public import FLT.Mazur.ModuleLineBundleOpenCover

/-!
# Gluing locally split line subbundles

Compatible local line inclusions construct a global line sheaf with an actual
ambient monomorphism. Chart recovery preserves local splittings; equality of
local subobjects determines the global object uniquely as an ambient subobject.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.LineSubbundleGluing
open CoherentSubmoduleGluing FCurve
variable {X : Scheme.{u}} {I : Type u} {U : I → X.Opens}
variable {M : X.Modules} {L : ∀ i, (U i).toScheme.Modules}
variable {a : ∀ i, L i ⟶ M.restrict (U i).ι} [∀ i, Mono (a i)]
variable (ha : CompatibleInclusions U M L a) (hU : iSup U = ⊤)

/-- The actual line sheaf constructed by gluing the prescribed ambient subobjects. -/
abbrev line : X.Modules := (data ha).glued

include hU in
/-- The glued object is a line bundle when every prescribed local object is. -/
theorem rankOne (hL : ∀ i, LocallyFreeRankOne (L i)) : LocallyFreeRankOne (line ha) := by
  apply LocallyFreeRankOne.of_openImmersionCover (fun i ↦ (U i).toScheme)
    (fun i ↦ (U i).ι)
  · intro x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show x ∈ iSup U by rw [hU]; trivial)
    exact ⟨i, ⟨x, hi⟩, rfl⟩
  · intro i
    exact (hL i).of_iso ((data ha).restrictionIso i).symm

/-- Local splittings are recovered on the original cover of the glued inclusion. -/
def restrictionSplit [∀ i, IsSplitMono (a i)] (i : I) :
    SplitMono ((restrictFunctor (U i).ι).map (inclusion ha hU)) where
  retraction := CategoryTheory.retraction (a i) ≫ ((data ha).restrictionIso i).inv
  id := by
    rw [← restriction_commutes ha hU i]
    simp only [Category.assoc, IsSplitMono.id_assoc, Iso.hom_inv_id]

instance [∀ i, IsSplitMono (a i)] (i : I) :
    IsSplitMono ((restrictFunctor (U i).ι).map (inclusion ha hU)) :=
  IsSplitMono.mk' (restrictionSplit ha hU i)

/-- A second ambient subobject with the same local images equals the constructed subobject. -/
theorem subobject_unique {N : X.Modules} (b : N ⟶ M) [Mono b]
    (hb : ∀ i, Subobject.mk ((restrictFunctor (U i).ι).map b) = Subobject.mk (a i)) :
    Subobject.mk b = Subobject.mk (inclusion ha hU) :=
  ModuleSubobjectCoverEquality.subobject_eq_of_openCover b (inclusion ha hU) U hU
    (fun i ↦ (hb i).trans (subobject_eq ha hU i).symm)

/-- The actual ambient subobject equality gives its canonical global comparison. -/
def comparison {N : X.Modules} (b : N ⟶ M) [Mono b]
    (hb : ∀ i, Subobject.mk ((restrictFunctor (U i).ι).map b) = Subobject.mk (a i)) :
    N ≅ line ha :=
  Subobject.isoOfMkEqMk b (inclusion ha hU) (subobject_unique ha hU b hb)

/-- The global comparison retains the original ambient inclusion. -/
lemma comparison_inclusion {N : X.Modules} (b : N ⟶ M) [Mono b]
    (hb : ∀ i, Subobject.mk ((restrictFunctor (U i).ι).map b) = Subobject.mk (a i)) :
    (comparison ha hU b hb).hom ≫ inclusion ha hU = b := by
  simp only [comparison, Subobject.isoOfMkEqMk_hom, Subobject.ofMkLEMk_comp]

/-- There is only one global comparison preserving the original ambient inclusion. -/
lemma comparison_unique {N : X.Modules} (b : N ⟶ M) [Mono b]
    (hb : ∀ i, Subobject.mk ((restrictFunctor (U i).ι).map b) = Subobject.mk (a i))
    (g : N ⟶ line ha) (hg : g ≫ inclusion ha hU = b) :
    g = (comparison ha hU b hb).hom := by
  apply (cancel_mono (inclusion ha hU)).mp
  rw [hg, comparison_inclusion]

end FLT.Mazur.LineSubbundleGluing
