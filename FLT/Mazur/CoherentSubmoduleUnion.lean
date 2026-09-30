/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedDescentGluingData
public import FLT.Mazur.CoherentSubmoduleGluing

/-!
# Coherent enlargement on the union with an affine open

The affine overlap extension supplies compatible subobjects. Their glued module
extends the original inclusion, with its actual restriction and overlap squares.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules FLT.Mazur.ModuleSheafMorphismGluing
open FLT.Mazur.CoherentSubmoduleGluing
open FLT.Mazur.FCurve.CoherentDevissage.ClosedDescentCharts
universe u
namespace FLT.Mazur.CoherentSubmoduleUnion
variable {X : Scheme.{u}} (M : X.Modules)

/-- Identify a restricted chart pushforward with the original module on a subopen. -/
def chartOn {U V : X.Opens} (h : V ≤ U) (L : U.toScheme.Modules) :
    ((pushforward U.ι).obj L).restrict V.ι ≅ L.restrict (X.homOfLE h) :=
  ((nestedRestriction h).app _).symm ≪≫
    (restrictFunctor (X.homOfLE h)).mapIso ((restrictFunctorAdjCounitIso U.ι).app L)

/-- Restrict an inclusion using the canonical nested-restriction comparison. -/
def mapOn {U V : X.Opens} (h : V ≤ U) {L : U.toScheme.Modules}
    (a : L ⟶ M.restrict U.ι) : L.restrict (X.homOfLE h) ⟶ M.restrict V.ι :=
  (restrictFunctor (X.homOfLE h)).map a ≫ (nestedRestriction h).hom.app M

/-- Slice transport agrees with geometric restriction of the original inclusion. -/
lemma inclusionOn_subopen {U V : X.Opens} (h : V ≤ U) {L : U.toScheme.Modules}
    (a : L ⟶ M.restrict U.ι) :
    restrictionEquiv V (inclusionOn M a h) = (chartOn h L).hom ≫ mapOn M h a := by
  let b := (restrictFunctorAdjCounitIso U.ι).hom.app L ≫ a
  let c := (chartOn h L).hom ≫ mapOn M h a
  have hb : sliceMap U b = inclusionOn M a le_rfl := by
    apply (restrictionEquiv U).injective
    rw [sliceMap_restrictionEquiv, inclusionOn_restriction]
  have hn : (restrictFunctor (X.homOfLE h)).map b ≫ (nestedRestriction h).hom.app M =
      (nestedRestriction h).hom.app _ ≫ c := by
    simp only [b, c, chartOn, mapOn, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Functor.map_comp, Iso.app_inv, Iso.app_hom, Category.assoc, Iso.hom_inv_id_app_assoc]
  have hc : inclusionOn M a h = sliceMap V c := by
    apply SheafOfModules.hom_ext
    ext W s
    have ht := sliceMap_nested h b c hn W.unop.left (leOfHom W.unop.hom)
    rw [hb, inclusionOn_localApp M a le_rfl h
      ((leOfHom W.unop.hom).trans h) (leOfHom W.unop.hom)] at ht
    exact congrArg (fun f ↦ f s) ht
  rw [hc, sliceMap_restrictionEquiv]

/-- Geometric restriction of a chart inclusion is monic. -/
instance mapOn_mono {U V : X.Opens} (h : V ≤ U) {L : U.toScheme.Modules}
    (a : L ⟶ M.restrict U.ι) [Mono a] : Mono (mapOn M h a) := by
  have := CoherentSubmoduleEnlargement.restrictMap_mono (X.homOfLE h) a
  dsimp [mapOn]
  infer_instance

/-- The two descriptions give the same subobject on a subopen. -/
lemma subobject_inclusionOn {U V : X.Opens} (h : V ≤ U) {L : U.toScheme.Modules}
    (a : L ⟶ M.restrict U.ι) [Mono a] :
    Subobject.mk (restrictionEquiv V (inclusionOn M a h)) = Subobject.mk (mapOn M h a) := by
  exact Subobject.mk_eq_mk_of_comm _ _ (chartOn h L) (inclusionOn_subopen M h a).symm

/-- Map a common subopen into the inverse-image overlap. -/
def overlapLift (U V W : X.Opens) (hU : W ≤ U) (hV : W ≤ V) :
    W.toScheme ⟶ (V.ι ⁻¹ᵁ U).toScheme :=
  (isPullback_morphismRestrict V.ι U).lift (X.homOfLE hU) (X.homOfLE hV)
    (by simp)

/-- The overlap lift recovers the inclusion into the first open. -/
lemma overlapLift_left (U V W : X.Opens) (hU : W ≤ U) (hV : W ≤ V) :
    overlapLift U V W hU hV ≫ (V.ι ∣_ U) = X.homOfLE hU :=
  (isPullback_morphismRestrict V.ι U).lift_fst _ _ _

/-- The overlap lift recovers the inclusion into the second open. -/
lemma overlapLift_right (U V W : X.Opens) (hU : W ≤ U) (hV : W ≤ V) :
    overlapLift U V W hU hV ≫ (V.ι ⁻¹ᵁ U).ι = X.homOfLE hV :=
  (isPullback_morphismRestrict V.ι U).lift_snd _ _ _

/-- The common-subopen map is an open immersion. -/
instance overlapLift_open (U V W : X.Opens) (hU : W ≤ U) (hV : W ≤ V) :
    IsOpenImmersion (overlapLift U V W hU hV) := by
  have : IsOpenImmersion (overlapLift U V W hU hV ≫ (V.ι ⁻¹ᵁ U).ι) := by
    rw [overlapLift_right]
    infer_instance
  exact IsOpenImmersion.of_comp _ (V.ι ⁻¹ᵁ U).ι

/-- Compare direct restriction with restriction along a commuting composite. -/
def along {A B C : Scheme.{u}} (r : A ⟶ B) (g : B ⟶ C) (f : A ⟶ C)
    [IsOpenImmersion r] [IsOpenImmersion g] [IsOpenImmersion f] (h : r ≫ g = f) :
    restrictFunctor f ≅ restrictFunctor g ⋙ restrictFunctor r :=
  (restrictFunctorCongr h).symm ≪≫ restrictFunctorComp r g

set_option maxHeartbeats 800000 in
-- Nested restriction comparisons require additional module-structure reduction.
/-- The constructed affine comparison identifies both subobjects on every subopen. -/
lemma overlap_subobject (U V W : X.Opens) (hU : W ≤ U) (hV : W ≤ V)
    (L : U.toScheme.Modules) (a : L ⟶ M.restrict U.ι) [Mono a]
    (E : CoherentSubmoduleEnlargement.Extension (M.restrict V.ι) (V.ι ⁻¹ᵁ U)
      (L.restrict (V.ι ∣_ U))
      ((restrictFunctor (V.ι ∣_ U)).map a ≫
        (CoherentSubmoduleEnlargement.restrictionSquare V.ι U).hom.app M)) :
    Subobject.mk (mapOn M hV E.inclusion) = Subobject.mk (mapOn M hU a) := by
  let r := overlapLift U V W hU hV
  let F := restrictFunctor r
  let qV := along r (V.ι ⁻¹ᵁ U).ι (X.homOfLE hV) (overlapLift_right U V W hU hV)
  let qU := along r (V.ι ∣_ U) (X.homOfLE hU) (overlapLift_left U V W hU hV)
  let e := qV.app E.obj ≪≫ F.mapIso E.comparison ≪≫ (qU.app L).symm
  apply Subobject.mk_eq_mk_of_comm _ _ e
  have ht : qU.inv.app (M.restrict U.ι) ≫ (nestedRestriction hU).hom.app M =
      F.map ((CoherentSubmoduleEnlargement.restrictionSquare V.ι U).hom.app M) ≫
        qV.inv.app (M.restrict V.ι) ≫ (nestedRestriction hV).hom.app M := by
    apply Scheme.Modules.hom_ext
    intro T
    simp only [qU, qV, along, F, CoherentSubmoduleEnlargement.restrictionSquare,
      nestedRestriction, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      NatTrans.comp_app, Hom.comp_app, CoherentSubmoduleEnlargement.restriction_app,
      restrictFunctorComp_hom_app_app, restrictFunctorComp_inv_app_app,
      restrictFunctorCongr_hom_app_app,
      restrict_map, ← Functor.map_comp]
    congr 1
  have hn := qV.hom.naturality E.inclusion
  have hu := qU.inv.naturality a
  simp only [Functor.comp_map] at hn hu
  dsimp only [e, mapOn]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Category.assoc]
  rw [← Category.assoc (qU.inv.app L), ← hu, Category.assoc, ht]
  rw [← F.map_comp_assoc ((restrictFunctor (V.ι ∣_ U)).map a),
    ← F.map_comp_assoc, E.commutes, ← Category.assoc, ← hn]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

/-- Compatible inclusions on two opens covering the scheme give an extension. -/
theorem extension_of_cover (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (L : U.toScheme.Modules) [L.IsFinitePresentation] (a : L ⟶ M.restrict U.ι) [Mono a]
    (E : CoherentSubmoduleEnlargement.Extension (M.restrict V.ι) (V.ι ⁻¹ᵁ U)
      (L.restrict (V.ι ∣_ U))
      ((restrictFunctor (V.ι ∣_ U)).map a ≫
        (CoherentSubmoduleEnlargement.restrictionSquare V.ι U).hom.app M)) :
    Nonempty (CoherentSubmoduleEnlargement.Extension M U L a) := by
  let C : ULift.{u} Bool → X.Opens := fun b ↦ cond b.down V U
  let D : ∀ b, (C b).toScheme.Modules := fun | ⟨false⟩ => L | ⟨true⟩ => E.obj
  let a' : ∀ b, D b ⟶ M.restrict (C b).ι :=
    fun | ⟨false⟩ => a | ⟨true⟩ => E.inclusion
  have (b : ULift.{u} Bool) : Mono (a' b) := by
    rcases b with ⟨b⟩; cases b <;> dsimp [a'] <;> infer_instance
  have (b : ULift.{u} Bool) : (D b).IsFinitePresentation := by
    rcases b with ⟨b⟩
    cases b <;> dsimp [D] <;> infer_instance
  have hC : iSup C = ⊤ := by
    simpa only [C, iSup_ulift, iSup_bool_eq, Bool.cond_true, Bool.cond_false, sup_comm] using hUV
  have hc : CompatibleInclusions C M D a' := by
    rintro ⟨b⟩ ⟨c⟩
    rw [subobject_inclusionOn, subobject_inclusionOn]
    cases b <;> cases c
    · rfl
    · exact (overlap_subobject M U V (U ⊓ V) inf_le_left inf_le_right L a E).symm
    · exact overlap_subobject M U V (V ⊓ U) inf_le_right inf_le_left L a E
    · rfl
  obtain ⟨N, hN, b, hb, e, he⟩ := exists_glued hc hC
  exact ⟨⟨N, b, hb, hN, e ⟨false⟩, he ⟨false⟩⟩⟩

/-- Restricting a containing open to a smaller open gives an isomorphism. -/
lemma restriction_isIso_of_le {U W : X.Opens} (h : U ≤ W) : IsIso (W.ι ∣_ U) := by
  let e := W.ι.isoImage (W.ι ⁻¹ᵁ U) ≪≫ X.isoOfEq
    ((W.functor_map_eq_inf U).trans (inf_eq_left.mpr h))
  have he : e.hom = W.ι ∣_ U := by
    apply (cancel_mono U.ι).mp
    simp [e, morphismRestrict_ι]
  rw [← he]
  infer_instance

/-- An enlargement on the union, with its inclusion and original restriction square. -/
structure UnionExtension (U V : X.Opens) (L : U.toScheme.Modules)
    (a : L ⟶ M.restrict U.ι) where
  /-- The constructed coherent module on the union. -/
  obj : (U ⊔ V).toScheme.Modules
  /-- Its inclusion in the restricted ambient module. -/
  inclusion : obj ⟶ M.restrict (U ⊔ V).ι
  /-- The inclusion is monic. -/
  inclusion_mono : Mono inclusion
  /-- The module has finite local presentations. -/
  coherent : obj.IsFinitePresentation
  /-- Restriction to the original open recovers the original module. -/
  comparison : obj.restrict (X.homOfLE (le_sup_left : U ≤ U ⊔ V)) ≅ L
  /-- The comparison identifies the actual inclusions. -/
  commutes : comparison.hom ≫ a =
    (restrictFunctor (X.homOfLE (le_sup_left : U ≤ U ⊔ V))).map inclusion ≫
      (nestedRestriction (le_sup_left : U ≤ U ⊔ V)).hom.app M

attribute [instance] UnionExtension.inclusion_mono UnionExtension.coherent

/-- The enlarged inclusion remains monic on the original open. -/
instance UnionExtension.restrict_mono {U V : X.Opens} {L : U.toScheme.Modules}
    {a : L ⟶ M.restrict U.ι} (E : UnionExtension M U V L a) :
    Mono ((restrictFunctor (X.homOfLE (le_sup_left : U ≤ U ⊔ V))).map E.inclusion) :=
  CoherentSubmoduleEnlargement.restrictMap_mono _ E.inclusion

/-- The enlarged submodule restricts to the original subobject. -/
theorem UnionExtension.subobject_eq {U V : X.Opens} {L : U.toScheme.Modules}
    {a : L ⟶ M.restrict U.ι} [Mono a] (E : UnionExtension M U V L a) :
    Subobject.mk ((restrictFunctor (X.homOfLE (le_sup_left : U ≤ U ⊔ V))).map
      E.inclusion ≫ (nestedRestriction le_sup_left).hom.app M) = Subobject.mk a :=
  Subobject.mk_eq_mk_of_comm _ _ E.comparison E.commutes

/-- The inclusion square still commutes on the intersection with the affine open. -/
theorem UnionExtension.overlap_commutes {U V : X.Opens} {L : U.toScheme.Modules}
    {a : L ⟶ M.restrict U.ι} (E : UnionExtension M U V L a) :
    (restrictFunctor (X.homOfLE (inf_le_left : U ⊓ V ≤ U))).map E.comparison.hom ≫
      mapOn M inf_le_left a =
    (restrictFunctor (X.homOfLE (inf_le_left : U ⊓ V ≤ U))).map
      ((restrictFunctor (X.homOfLE le_sup_left)).map E.inclusion ≫
        (nestedRestriction le_sup_left).hom.app M) ≫
      (nestedRestriction inf_le_left).hom.app M := by
  rw [mapOn, ← Category.assoc, ← Functor.map_comp, E.commutes]

set_option maxHeartbeats 800000 in
-- Nested restriction comparisons require additional module-structure reduction.
/-- A coherent submodule extends over the union with any affine open. -/
theorem exists_union_extension [IsLocallyNoetherian X] [M.IsFinitePresentation]
    (U V : X.Opens) (hV : IsAffineOpen V) (L : U.toScheme.Modules)
    [L.IsFinitePresentation] (a : L ⟶ M.restrict U.ι) [Mono a] :
    Nonempty (UnionExtension M U V L a) := by
  let W := U ⊔ V
  let u := W.ι ⁻¹ᵁ U
  let v := W.ι ⁻¹ᵁ V
  let f := W.ι ∣_ U
  let g := X.homOfLE (le_sup_left : U ≤ W)
  have hf : IsIso f := restriction_isIso_of_le le_sup_left
  have hfv : IsIso (W.ι ∣_ V) := restriction_isIso_of_le le_sup_right
  have hAff : IsAffineOpen v := by
    have : IsAffine V.toScheme := hV
    exact IsAffine.of_isIso (W.ι ∣_ V)
  have hN := isLocallyNoetherian_of_isOpenImmersion W.ι
  have hM := FCurve.CoherentDevissage.coherentPresentation_restrict W.ι M
  have hL := FCurve.CoherentDevissage.coherentPresentation_restrict f L
  let a' := (restrictFunctor f).map a ≫
    (CoherentSubmoduleEnlargement.restrictionSquare W.ι U).hom.app M
  have ha' : Mono a' := by
    have := CoherentSubmoduleEnlargement.restrictMap_mono f a
    dsimp [a']
    infer_instance
  obtain ⟨E⟩ := CoherentSubmoduleEnlargement.exists_affine_overlap_extension
    (M.restrict W.ι) u v hAff (L.restrict f) a'
  have huv : u ⊔ v = ⊤ := by
    rw [← Scheme.Hom.preimage_sup]
    exact Scheme.Opens.ι_preimage_self W
  obtain ⟨G⟩ := extension_of_cover (M.restrict W.ι) u v huv (L.restrict f) a' E
  have hfg : f ≫ g = u.ι := by
    apply (cancel_mono W.ι).mp
    change (W.ι ∣_ U) ≫ X.homOfLE le_sup_left ≫ W.ι = (W.ι ⁻¹ᵁ U).ι ≫ W.ι
    rw [Scheme.homOfLE_ι]
    exact morphismRestrict_ι W.ι U
  let q := (restrictFunctorComp f g).symm ≪≫ restrictFunctorCongr hfg
  have (P : U.toScheme.Modules) : IsIso ((restrictAdjunction f).unit.app P) :=
    CoherentSubmoduleEnlargement.iso_unit_isIso f P
  have : IsIso (restrictAdjunction f).unit := NatIso.isIso_of_isIso_app _
  let FF := (restrictAdjunction f).fullyFaithfulLOfIsIsoUnit
  let e := FF.preimageIso (q.app G.obj ≪≫ G.comparison)
  refine ⟨⟨G.obj, G.inclusion, G.inclusion_mono, G.coherent, e, ?_⟩⟩
  have ht : (restrictFunctor f).map ((nestedRestriction le_sup_left).hom.app M) ≫
      (CoherentSubmoduleEnlargement.restrictionSquare W.ι U).hom.app M =
        q.hom.app (M.restrict W.ι) := by
    apply Scheme.Modules.hom_ext
    intro T
    simp only [q, nestedRestriction, CoherentSubmoduleEnlargement.restrictionSquare,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Hom.comp_app,
      CoherentSubmoduleEnlargement.restriction_app, restrictFunctorComp_hom_app_app,
      restrictFunctorComp_inv_app_app, restrictFunctorCongr_hom_app_app,
      restrict_map, ← Functor.map_comp]
    congr 1
  apply FF.map_injective
  apply (cancel_mono
    ((CoherentSubmoduleEnlargement.restrictionSquare W.ι U).hom.app M)).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [ht]
  have he : (restrictFunctor f).map e.hom = q.hom.app G.obj ≫ G.comparison.hom :=
    FF.map_preimage _
  rw [he, Category.assoc]
  change q.hom.app G.obj ≫ G.comparison.hom ≫ a' = _
  rw [G.commutes]
  exact (q.hom.naturality G.inclusion).symm

end FLT.Mazur.CoherentSubmoduleUnion
