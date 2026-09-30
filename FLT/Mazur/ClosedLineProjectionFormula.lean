/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedPushforwardRestriction
public import FLT.Mazur.ModuleLineBundlePullback
public import FLT.Mazur.ModuleSheafOpenIsoDetection
public import FLT.Mazur.ProjectiveTwistTensor

/-!
# Projection along a scheme morphism

The canonical projection map is induced by the bilinear pairing of sections
with the pullback adjunction unit. It is invertible for locally free rank-one
coefficients, as checked on a trivializing cover. The comparison commutes with
open restriction. No closed-immersion assumption is needed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace FLT.Mazur.FCurve.ClosedLineProjectionFormula

open ModuleSheafTensor
open CoherentDevissage

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (L : Y.Modules)

/-- The canonical projection map, defined without a local trivialization. -/
def comparison : tensor ((pushforward f).obj F) L ⟶
    (pushforward f).obj (tensor F ((pullback f).obj L)) :=
  lift (((pairing F ((pullback f).obj L)).pushforward f).precomp
    (𝟙 _) ((pullbackPushforwardAdjunction f).unit.app L))

/-- The projection map tensors a section with the pullback-unit section. -/
lemma comparison_pure (U : Y.Opens) (m : Γ((pushforward f).obj F, U)) (l : Γ(L, U)) :
    (comparison f F L).app U (pure _ L U m l) =
      pure F ((pullback f).obj L) (f ⁻¹ᵁ U) m
        (((pullbackPushforwardAdjunction f).unit.app L).app U l) := by
  rw [comparison, lift_pure]
  rfl

/-- Naturality in the line coefficient. -/
@[reassoc]
lemma comparison_naturality {L' : Y.Modules} (a : L ⟶ L') :
    map (𝟙 ((pushforward f).obj F)) a ≫ comparison f F L' =
      comparison f F L ≫ (pushforward f).map (map (𝟙 F) ((pullback f).map a)) := by
  apply ModuleSheafTensor.hom_ext
  intro U m l
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, map_pure, comparison_pure,
    Hom.id_app, ConcreteCategory.id_apply, pushforward_map_app]
  erw [map_pure]
  simp only [Hom.id_app, ConcreteCategory.id_apply]
  exact congrArg (pure F ((pullback f).obj L') (f ⁻¹ᵁ U) m)
    (congrArg (fun k ↦ k.app U l) ((pullbackPushforwardAdjunction f).unit.naturality a))

/-- On the structure module, the projection comparison agrees with the unitors. -/
lemma comparison_unit :
    comparison f F (structureModule Y) ≫
      (pushforward f).map (rightTrivialIso F (modulePullbackUnitIso f)).hom =
        (rightUnitor ((pushforward f).obj F)).hom := by
  apply ModuleSheafTensor.hom_ext
  intro U m r
  change Γ(F, f ⁻¹ᵁ U) at m
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, comparison_pure,
    pushforward_map_app]
  have h := congrArg (fun k ↦ k.val.app (op U) r)
    (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      f.toRingCatSheafHom)
  change (modulePullbackUnitIso f).hom.app (f ⁻¹ᵁ U)
    (((pullbackPushforwardAdjunction f).unit.app (structureModule Y)).app U r) =
      f.app U r at h
  exact (rightTrivialIso_pure F (modulePullbackUnitIso f) (f ⁻¹ᵁ U) m
    (((pullbackPushforwardAdjunction f).unit.app (structureModule Y)).app U r)).trans
      ((congrArg (fun a : Γ(X, f ⁻¹ᵁ U) ↦ a • (m : Γ(F, f ⁻¹ᵁ U))) h).trans
        (rightUnitor_pure ((pushforward f).obj F) U r m).symm)

/-- The projection comparison is invertible for the structure module. -/
instance comparison_unit_isIso : IsIso (comparison f F (structureModule Y)) := by
  have : IsIso (comparison f F (structureModule Y) ≫
      (pushforward f).map (rightTrivialIso F (modulePullbackUnitIso f)).hom) := by
    rw [comparison_unit]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((pushforward f).map
    (rightTrivialIso F (modulePullbackUnitIso f)).hom)

/-- Any global trivialization proves invertibility of the canonical comparison. -/
lemma comparison_isIso_of_trivial (e : L ≅ structureModule Y) :
    IsIso (comparison f F L) := by
  have : IsIso (map (𝟙 ((pushforward f).obj F)) e.hom) :=
    show IsIso (congr (Iso.refl _) e).hom from inferInstance
  have : IsIso (map (𝟙 F) ((pullback f).map e.hom)) :=
    show IsIso (congr (Iso.refl _) ((pullback f).mapIso e)).hom from inferInstance
  have : IsIso (comparison f F L ≫
      (pushforward f).map (map (𝟙 F) ((pullback f).map e.hom))) := by
    rw [← comparison_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((pushforward f).map
    (map (𝟙 F) ((pullback f).map e.hom)))

/-- The pushforward comparison for the commuting open restriction square. -/
def openSquare (U : Y.Opens) :
    pushforward (f ∣_ U) ⋙ pushforward U.ι ≅
      pushforward (f ⁻¹ᵁ U).ι ⋙ pushforward f :=
  pushforwardComp (f ∣_ U) U.ι ≪≫
    pushforwardCongr (morphismRestrict_ι f U) ≪≫
    (pushforwardComp (f ⁻¹ᵁ U).ι f).symm

/-- The pullback comparison obtained by taking mates of the commuting square. -/
def openPullbackIso (U : Y.Opens) :
    ((pullback f).obj L).restrict (f ⁻¹ᵁ U).ι ≅
      (pullback (f ∣_ U)).obj (L.restrict U.ι) :=
  ((conjugateIsoEquiv
    ((restrictAdjunction U.ι).comp (pullbackPushforwardAdjunction (f ∣_ U)))
    ((pullbackPushforwardAdjunction f).comp (restrictAdjunction (f ⁻¹ᵁ U).ι))).symm
      (openSquare f U)).app L

/-- The open pullback comparison intertwines the two composite adjunction units. -/
lemma openPullbackIso_unit (U : Y.Opens) :
    ((restrictAdjunction U.ι).comp (pullbackPushforwardAdjunction (f ∣_ U))).unit.app L ≫
      (openSquare f U).hom.app _ =
    ((pullbackPushforwardAdjunction f).comp (restrictAdjunction (f ⁻¹ᵁ U).ι)).unit.app L ≫
      (pushforward (f ⁻¹ᵁ U).ι ⋙ pushforward f).map
        (openPullbackIso f L U).hom :=
  unit_conjugateEquiv_symm _ _ (openSquare f U).hom L

set_option maxHeartbeats 400000 in
-- Comparing the composite adjunction units involves two scalar restrictions.
/-- On the open restriction square, the pullback unit commutes with restriction. -/
lemma open_unit (U : Y.Opens) :
    (restrictFunctor U.ι).map ((pullbackPushforwardAdjunction f).unit.app L) ≫
      (closedPushforwardRestriction f U).hom.app ((pullback f).obj L) ≫
      (pushforward (f ∣_ U)).map (openPullbackIso f L U).hom =
    (pullbackPushforwardAdjunction (f ∣_ U)).unit.app (L.restrict U.ι) := by
  apply ((restrictAdjunction U.ι).homEquiv _ _).injective
  apply Scheme.Modules.hom_ext
  intro V
  ext l
  have h := congrArg (fun k ↦ k.app V l) (openPullbackIso_unit f L U)
  simp only [Adjunction.comp_unit_app, Hom.comp_app, ConcreteCategory.comp_apply,
    pushforward_map_app, restrictAdjunction_unit_app_app] at h
  simp only [openSquare, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
    pushforwardCongr_hom_app_app, Hom.comp_app, ConcreteCategory.comp_apply,
    Functor.comp_map, pushforward_map_app] at h
  simp only [Adjunction.homEquiv_unit, Hom.comp_app, ConcreteCategory.comp_apply,
    pushforward_map_app, restrictAdjunction_unit_app_app,
    closedPushforwardRestriction_hom_app]
  have hn := ConcreteCategory.congr_hom
    (((pullbackPushforwardAdjunction f).unit.app L).mapPresheaf.naturality
      (homOfLE (U.ι.image_preimage_le V)).op) l
  dsimp only [Hom.mapPresheaf, NatTrans.app] at hn
  simp only [ConcreteCategory.comp_apply] at hn
  erw [hn]
  let P := (pullback (f ∣_ U)).obj (L.restrict U.ι)
  have he : (f ⁻¹ᵁ U).ι ⁻¹ᵁ f ⁻¹ᵁ V = (f ∣_ U) ⁻¹ᵁ U.ι ⁻¹ᵁ V :=
    congrArg (fun k ↦ k ⁻¹ᵁ V) (morphismRestrict_ι f U).symm
  apply (ConcreteCategory.bijective_of_isIso (P.presheaf.map (eqToHom he).op)).injective
  have heq := ConcreteCategory.congr_hom
    ((openPullbackIso f L U).hom.mapPresheaf.naturality (eqToHom he).op)
  simp only [ConcreteCategory.comp_apply] at heq
  erw [← heq]
  simp only [Functor.comp_obj, restrict_map, pushforward_obj_presheaf_map,
    toPresheaf_map, mapPresheaf_app]
  have comp (M : X.Modules) {A B C : X.Opens} (a : A ⟶ B) (b : B ⟶ C)
      (m : Γ(M, C)) :
      M.presheaf.map a.op (M.presheaf.map b.op m) = M.presheaf.map (a ≫ b).op m := by
    exact (ConcreteCategory.congr_hom (M.presheaf.map_comp b.op a.op) m).symm
  conv_lhs =>
    arg 2
    erw [comp ((pullback f).obj L), comp ((pullback f).obj L)]
  exact h.symm


/-- Restriction comparison for the source of the projection map. -/
def sourceOpenIso (U : Y.Opens) :
    (tensor ((pushforward f).obj F) L).restrict U.ι ≅
      tensor ((pushforward (f ∣_ U)).obj (F.restrict (f ⁻¹ᵁ U).ι)) (L.restrict U.ι) :=
  restrictIso _ _ U.ι ≪≫ congr ((closedPushforwardRestriction f U).app F) (Iso.refl _)

/-- Restriction comparison for the target of the projection map. -/
def targetOpenIso (U : Y.Opens) :
    ((pushforward f).obj (tensor F ((pullback f).obj L))).restrict U.ι ≅
      (pushforward (f ∣_ U)).obj
        (tensor (F.restrict (f ⁻¹ᵁ U).ι) ((pullback (f ∣_ U)).obj (L.restrict U.ι))) :=
  (closedPushforwardRestriction f U).app _ ≪≫
    (pushforward (f ∣_ U)).mapIso (restrictIso _ _ (f ⁻¹ᵁ U).ι ≪≫
      congr (Iso.refl _) (openPullbackIso f L U))

set_option maxHeartbeats 400000 in
-- Section transports compare the two chosen restriction isomorphisms.
/-- The canonical projection map commutes with open restriction. -/
@[reassoc]
lemma comparison_restrict (U : Y.Opens) :
    (restrictFunctor U.ι).map (comparison f F L) ≫ (targetOpenIso f F L U).hom =
      (sourceOpenIso f F L U).hom ≫
        comparison (f ∣_ U) (F.restrict (f ⁻¹ᵁ U).ι) (L.restrict U.ι) := by
  apply restrict_hom_ext U.ι
  intro V m l
  change Γ(F, f ⁻¹ᵁ (U.ι ''ᵁ V)) at m
  simp only [sourceOpenIso, targetOpenIso, Iso.trans_hom, Functor.mapIso_hom,
    Hom.comp_app, ConcreteCategory.comp_apply, pushforward_map_app,
    restrictIso_hom_pure, ModuleSheafTensor.congr, ModuleSheafTensor.map_pure]
  change (map (𝟙 _) (openPullbackIso f L U).hom).app _
    ((restrictIso F ((pullback f).obj L) (f ⁻¹ᵁ U).ι).hom.app _
      ((tensor F ((pullback f).obj L)).presheaf.map _
        ((comparison f F L).app _ (pure _ _ _ m l)))) = _
  rw [comparison_pure]
  conv_lhs =>
    arg 2
    arg 2
    erw [pure_restrict F ((pullback f).obj L)]
  conv_lhs =>
    arg 2
    erw [restrictIso_hom_pure F ((pullback f).obj L)]
  erw [ModuleSheafTensor.map_pure, comparison_pure]
  have h := congrArg (fun k ↦ k.app V l) (open_unit f L U)
  exact congrArg (pure _ _ _ _) h

/-- The projection formula holds for every locally free rank-one coefficient. -/
lemma comparison_isIso (hL : LocallyFreeRankOne L) : IsIso (comparison f F L) := by
  choose U hx e using hL
  apply ModuleSheafOpenIsoDetection.isIso_of_openCover (comparison f F L) U
    (fun x ↦ ⟨x, hx x⟩)
  intro x
  let := comparison_isIso_of_trivial (f ∣_ U x) (F.restrict (f ⁻¹ᵁ U x).ι)
    (L.restrict (U x).ι) (e x).some
  have : IsIso ((restrictFunctor (U x).ι).map (comparison f F L) ≫
      (targetOpenIso f F L (U x)).hom) := by
    rw [comparison_restrict]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (targetOpenIso f F L (U x)).hom

/-- The line projection formula, with pushforward on the left. -/
def projectionIso (hL : LocallyFreeRankOne L) :
    (pushforward f).obj (tensor F ((pullback f).obj L)) ≅
      tensor ((pushforward f).obj F) L := by
  letI := comparison_isIso f F L hL
  exact (asIso (comparison f F L)).symm

/-- The inverse of the projection isomorphism is the canonical bilinear map. -/
@[simp]
lemma projectionIso_inv (hL : LocallyFreeRankOne L) :
    (projectionIso f F L hL).inv = comparison f F L := rfl

/-- Open restriction compatibility for the projection isomorphism. -/
lemma projectionIso_restrict (hL : LocallyFreeRankOne L) (U : Y.Opens) :
    (restrictFunctor U.ι).map (projectionIso f F L hL).inv ≫ (targetOpenIso f F L U).hom =
      (sourceOpenIso f F L U).hom ≫
        (projectionIso (f ∣_ U) (F.restrict (f ⁻¹ᵁ U).ι) (L.restrict U.ι)
          (hL.restrict U.ι)).inv :=
  comparison_restrict f F L U

end FLT.Mazur.FCurve.ClosedLineProjectionFormula
