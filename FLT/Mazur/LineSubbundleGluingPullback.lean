/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSubbundleGluing
public import FLT.Mazur.LocallySplitInclusionPullback

/-!
# Geometric chart recovery after gluing and arbitrary base change

Pull back the constructed global line and recover its original local objects
on inverse-image opens. The recovery preserves the genuine ambient inclusion.
These local images uniquely characterize the pulled-back global subobject.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.LineSubbundleGluing
open CoherentSubmoduleGluing FCurve
variable {X T : Scheme.{u}} {I : Type u} {U : I → X.Opens}
variable {M : X.Modules} {L : ∀ i, (U i).toScheme.Modules}
variable {a : ∀ i, L i ⟶ M.restrict (U i).ι} [∀ i, IsSplitMono (a i)]
variable (ha : CompatibleInclusions U M L a) (hU : iSup U = ⊤) (f : T ⟶ X)

/-- Recover the actual original chart object on each inverse-image open. -/
def pullbackChartIso (i : I) :
    ((pullback f).obj (line ha)).restrict (f ⁻¹ᵁ U i).ι ≅
      (pullback (f ∣_ U i)).obj (L i) :=
  modulePullbackOpenIso f (U i) (line ha) ≪≫
    (pullback (f ∣_ U i)).mapIso ((data ha).restrictionIso i)

/-- The original chart inclusion, transported into the actual pulled-back ambient sheaf. -/
def pullbackLocalInclusion (i : I) :
    (pullback (f ∣_ U i)).obj (L i) ⟶
      ((pullback f).obj M).restrict (f ⁻¹ᵁ U i).ι :=
  (pullback (f ∣_ U i)).map (a i) ≫ (modulePullbackOpenIso f (U i) M).inv

instance (i : I) : IsSplitMono (pullbackLocalInclusion (a := a) f i) := by
  dsimp only [pullbackLocalInclusion]
  infer_instance

/-- Recovery after base change preserves the actual ambient morphism. -/
lemma pullbackChartIso_inclusion (i : I) :
    (pullbackChartIso ha f i).hom ≫ pullbackLocalInclusion (a := a) f i =
      (restrictFunctor (f ⁻¹ᵁ U i).ι).map ((pullback f).map (inclusion ha hU)) := by
  dsimp only [pullbackChartIso, pullbackLocalInclusion, Iso.trans_hom, Functor.mapIso_hom]
  rw [Category.assoc, ← Category.assoc ((pullback (f ∣_ U i)).map _),
    ← Functor.map_comp, restriction_commutes ha hU i]
  rw [← Category.assoc, ← LocallySplitInclusionPullback.open_naturality]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

instance pullbackInclusion_mono : Mono ((pullback f).map (inclusion ha hU)) :=
  LocallySplitInclusionPullback.mono_of_split_cover (inclusion ha hU) f U hU

/-- The local image formula identifies actual subobjects after arbitrary base change. -/
lemma pullback_subobject_chart (i : I) :
    Subobject.mk ((restrictFunctor (f ⁻¹ᵁ U i).ι).map
        ((pullback f).map (inclusion ha hU))) =
      Subobject.mk (pullbackLocalInclusion (a := a) f i) :=
  Subobject.mk_eq_mk_of_comm _ _ (pullbackChartIso ha f i)
    (pullbackChartIso_inclusion ha hU f i)

/-- Independently specified target subobjects are determined by these genuine local images. -/
lemma pullback_subobject_unique {N : T.Modules} (b : N ⟶ (pullback f).obj M) [Mono b]
    (hb : ∀ i, Subobject.mk ((restrictFunctor (f ⁻¹ᵁ U i).ι).map b) =
      Subobject.mk (pullbackLocalInclusion (a := a) f i)) :
    Subobject.mk b = Subobject.mk ((pullback f).map (inclusion ha hU)) := by
  apply ModuleSubobjectCoverEquality.subobject_eq_of_openCover b _ (fun i ↦ f ⁻¹ᵁ U i)
  · apply top_le_iff.mp
    intro x _
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show f x ∈ iSup U by rw [hU]; trivial)
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  · intro i
    exact (hb i).trans (pullback_subobject_chart ha hU f i).symm

end FLT.Mazur.LineSubbundleGluing
