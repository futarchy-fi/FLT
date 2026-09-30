/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleLineBundlePullback

/-!
# Structure-module comparisons under pullback

The chosen pullback comparison transports multiplication by a section to
multiplication by its pullback. The comparison agrees with open restriction
and composition, and determines changes of trivialization on a common chart.
These are prerequisites for restriction coherence of local trivializations.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve
variable {X Y Z : Scheme.{u}}
/-- The structure-module comparison sends an adjunction-unit section to its pullback. -/
lemma modulePullbackUnitIso_unit (f : X ⟶ Y) (U : Y.Opens) (r : Γ(Y, U)) :
    (modulePullbackUnitIso f).hom.app (f ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (structureModule Y)).app U r) = f.app U r := by
  exact congrArg (fun k ↦ k.val.app (op U) r)
    (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      f.toRingCatSheafHom)

/-- Conjugation by the structure-module comparison commutes with pulled-back sections. -/
lemma modulePullbackUnitIso_conjugate_app (f : X ⟶ Y)
    (a : structureModule Y ⟶ structureModule Y) (U : Y.Opens) (r : Γ(Y, U)) :
    ((modulePullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map a ≫
      (modulePullbackUnitIso f).hom).app (f ⁻¹ᵁ U) (f.app U r) =
        f.app U (a.app U r) := by
  rw [← modulePullbackUnitIso_unit f U r]
  have he := congrArg (fun k ↦ k.app (f ⁻¹ᵁ U)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      (structureModule Y)).app U r)) (modulePullbackUnitIso f).hom_inv_id
  have hn := congrArg (fun k ↦ k.app U r)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality a).symm
  change (modulePullbackUnitIso f).hom.app _
    (((Scheme.Modules.pullback f).map a).app _
      ((modulePullbackUnitIso f).inv.app _ ((modulePullbackUnitIso f).hom.app _ _))) = _
  change (modulePullbackUnitIso f).inv.app _ ((modulePullbackUnitIso f).hom.app _ _) = _ at he
  rw [he]
  change ((Scheme.Modules.pullback f).map a).app _
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app _).app U r) =
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app _).app U (a.app U r) at hn
  simp only [Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply]
  erw [hn, modulePullbackUnitIso_unit]

/-- A pulled-back endomorphism multiplies by its pulled-back scalar on every subopen. -/
lemma modulePullbackUnitIso_scalar (f : X ⟶ Y)
    (a : structureModule Y ⟶ structureModule Y) (U : Y.Opens)
    (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U) (r : Γ(X, V)) :
    ((modulePullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map a ≫
      (modulePullbackUnitIso f).hom).app V r =
        f.appLE U V h (a.app U (1 : Γ(Y, U))) * r := by
  let b := (modulePullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map a ≫
    (modulePullbackUnitIso f).hom
  have hb := modulePullbackUnitIso_conjugate_app f a U 1
  simp only [map_one] at hb
  have hn := ConcreteCategory.congr_hom (b.mapPresheaf.naturality (homOfLE h).op)
    (1 : Γ(X, f ⁻¹ᵁ U))
  change b.app V (X.presheaf.map (homOfLE h).op 1) =
    X.presheaf.map (homOfLE h).op (b.app (f ⁻¹ᵁ U) (1 : Γ(X, f ⁻¹ᵁ U))) at hn
  rw [map_one, hb] at hn
  change b.app V r = _
  calc
    b.app V r = r * (show Γ(X, V) from b.app V (1 : Γ(X, V))) := by
      have hs := b.app_smul r (1 : Γ(X, V))
      simpa only [smul_eq_mul, mul_one] using hs
    _ = _ := by rw [hn, mul_comm]; rfl

/-- The restriction and pullback comparisons agree on the structure module. -/
lemma restrictPullbackUnitIso (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctorIsoPullback f).hom.app (structureModule Y) ≫
      (modulePullbackUnitIso f).hom = (Scheme.Modules.restrictUnitIso f).hom := by
  apply ((Scheme.Modules.restrictAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  change ((Scheme.Modules.restrictAdjunction f).homEquiv _ _
    (((Scheme.Modules.restrictAdjunction f).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction f)).hom.app _)) ≫ _ = _
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  apply Scheme.Modules.hom_ext
  intro U
  ext r
  change (modulePullbackUnitIso f).hom.app (f ⁻¹ᵁ U)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app _).app U r) =
    (f.appIso (f ⁻¹ᵁ U)).hom (Y.presheaf.map
      (homOfLE (f.image_preimage_le U)).op r)
  rw [modulePullbackUnitIso_unit]
  rw [Scheme.Hom.appIso_hom', ← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
    ← Scheme.Hom.app_eq_appLE]

/-- The inverse composition comparison sends the composite unit to two successive units. -/
lemma modulePullbackComp_inv_unit (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (m : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp f g).inv.app M).app ((f ≫ g) ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M).app U m) =
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      ((Scheme.Modules.pullback g).obj M)).app (g ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app U m) := by
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  exact (congrArg (fun k ↦ k.app U m) h).symm

/-- The explicit restriction-composition comparison is the mate of pushforward composition. -/
lemma conjugateEquiv_restrictFunctorComp (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    conjugateEquiv ((Scheme.Modules.restrictAdjunction g).comp
      (Scheme.Modules.restrictAdjunction f)) (Scheme.Modules.restrictAdjunction (f ≫ g))
      (Scheme.Modules.restrictFunctorComp f g).hom =
        (Scheme.Modules.pushforwardComp f g).hom := by
  ext M U x
  simp only [conjugateEquiv_apply_app, Adjunction.comp_counit_app,
    Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.pushforward_map_app, Scheme.Modules.restrictAdjunction_unit_app_app,
    Scheme.Modules.restrictAdjunction_counit_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app,
    Scheme.Modules.pushforwardComp_hom_app_app]
  change M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _
    (M.presheaf.map _ x))) = x
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  convert M.presheaf.map_id (op ((f ≫ g) ⁻¹ᵁ U)) |> congrArg (fun k ↦ k x) using 1

set_option maxHeartbeats 600000 in
-- Transposing the composite comparison unfolds both pullback adjunctions.
/-- The structure-module comparison commutes with composition of pullbacks. -/
lemma modulePullbackUnitIso_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Scheme.Modules.pullbackComp f g).inv.app (structureModule Z) ≫
      (Scheme.Modules.pullback f).map (modulePullbackUnitIso g).hom ≫
        (modulePullbackUnitIso f).hom = (modulePullbackUnitIso (f ≫ g)).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _).injective
  apply Scheme.Modules.hom_ext
  intro U
  ext r
  change (modulePullbackUnitIso f).hom.app ((f ≫ g) ⁻¹ᵁ U)
    (((Scheme.Modules.pullback f).map (modulePullbackUnitIso g).hom).app _
      (((Scheme.Modules.pullbackComp f g).inv.app _).app _
        (((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app _).app U r))) =
    (modulePullbackUnitIso (f ≫ g)).hom.app _
      (((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app _).app U r)
  rw [modulePullbackComp_inv_unit, modulePullbackUnitIso_unit]
  have hn := congrArg (fun k ↦ k.app (g ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app _).app U r))
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality
      (modulePullbackUnitIso g).hom).symm
  change ((Scheme.Modules.pullback f).map _).app _
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app _).app _ _) =
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app _).app _
      ((modulePullbackUnitIso g).hom.app _ _) at hn
  exact (congrArg ((modulePullbackUnitIso f).hom.app (f ⁻¹ᵁ (g ⁻¹ᵁ U))) hn).trans
    ((modulePullbackUnitIso_unit f (g ⁻¹ᵁ U) _).trans
      (congrArg (f.app (g ⁻¹ᵁ U)) (modulePullbackUnitIso_unit g U r)))

/-- On a common chart, changing pulled-back trivializations multiplies by the pulled-back scalar. -/
lemma modulePullbackTrivialization_change (f : X ⟶ Y) {M : Y.Modules} {U : Y.Opens}
    (e e' : M.restrict U.ι ≅ structureModule U.toScheme)
    (A : U.toScheme.Opens) (V : (f ⁻¹ᵁ U).toScheme.Opens)
    (h : V ≤ (f ∣_ U) ⁻¹ᵁ A) (r : Γ((f ⁻¹ᵁ U).toScheme, V)) :
    ((modulePullbackTrivialization f e).inv ≫
      (modulePullbackTrivialization f e').hom).app V r =
    (f ∣_ U).appLE A V h ((e.inv ≫ e'.hom).app A (1 : Γ(U.toScheme, A))) * r := by
  have he : (modulePullbackTrivialization f e).inv ≫
      (modulePullbackTrivialization f e').hom =
      (modulePullbackUnitIso (f ∣_ U)).inv ≫
        (Scheme.Modules.pullback (f ∣_ U)).map (e.inv ≫ e'.hom) ≫
          (modulePullbackUnitIso (f ∣_ U)).hom := by
    simp [modulePullbackTrivialization, Functor.map_comp, Category.assoc]
  rw [he]
  exact modulePullbackUnitIso_scalar (f ∣_ U) (e.inv ≫ e'.hom) A V h r

/-- The restriction-to-pullback comparison is the mate of the identity pushforward map. -/
lemma conjugateEquiv_restrictFunctorIsoPullback (f : X ⟶ Y) [IsOpenImmersion f] :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.restrictAdjunction f) (Scheme.Modules.restrictFunctorIsoPullback f).hom =
        𝟙 (Scheme.Modules.pushforward f) := by
  simp [Scheme.Modules.restrictFunctorIsoPullback, Adjunction.leftAdjointUniq]

/-- The chosen restriction-to-pullback comparisons commute with composition. -/
lemma restrictFunctorIsoPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    ((Scheme.Modules.restrictFunctorComp f g).hom ≫
      Functor.whiskerRight (Scheme.Modules.restrictFunctorIsoPullback g).hom
        (Scheme.Modules.restrictFunctor f)) ≫
      Functor.whiskerLeft (Scheme.Modules.pullback g)
        (Scheme.Modules.restrictFunctorIsoPullback f).hom =
    (Scheme.Modules.restrictFunctorIsoPullback (f ≫ g)).hom ≫
      (Scheme.Modules.pullbackComp f g).inv := by
  apply (conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.restrictAdjunction (f ≫ g))).injective
  rw [← conjugateEquiv_comp _
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.restrictAdjunction f)) _]
  rw [← conjugateEquiv_comp _
    ((Scheme.Modules.restrictAdjunction g).comp (Scheme.Modules.restrictAdjunction f)) _]
  rw [← conjugateEquiv_comp _ (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)) _]
  rw [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
    conjugateEquiv_restrictFunctorIsoPullback,
    conjugateEquiv_restrictFunctorIsoPullback,
    conjugateEquiv_restrictFunctorIsoPullback,
    conjugateEquiv_restrictFunctorComp, Scheme.Modules.conjugateEquiv_pullbackComp_inv]
  simp

/-- The structure-module comparison respects equality of scheme morphisms. -/
lemma modulePullbackUnitIso_congr {f g : X ⟶ Y} (h : f = g) :
    (Scheme.Modules.pullbackCongr h).hom.app (structureModule Y) ≫
      (modulePullbackUnitIso g).hom = (modulePullbackUnitIso f).hom := by
  subst g
  simp [Scheme.Modules.pullbackCongr]

/-- The forward composition comparison commutes with the structure-module comparison. -/
lemma modulePullbackUnitIso_comp_hom (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Scheme.Modules.pullback f).map (modulePullbackUnitIso g).hom ≫
      (modulePullbackUnitIso f).hom =
    (Scheme.Modules.pullbackComp f g).hom.app (structureModule Z) ≫
      (modulePullbackUnitIso (f ≫ g)).hom := by
  rw [← cancel_epi ((Scheme.Modules.pullbackComp f g).inv.app (structureModule Z)),
    Iso.inv_hom_id_app_assoc]
  exact modulePullbackUnitIso_comp f g

/-- In an open-immersion square, the restriction comparison respects the structure module. -/
lemma modulePullbackRestrictIso_unit {W : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ W)
    (i : Z ⟶ X) (j : W ⟶ Y) [IsOpenImmersion i] [IsOpenImmersion j]
    (h : i ≫ f = g ≫ j) :
    (modulePullbackRestrictIso f g i j h (structureModule Y)).hom ≫
      (Scheme.Modules.pullback g).map (Scheme.Modules.restrictUnitIso j).hom ≫
        (modulePullbackUnitIso g).hom =
    (Scheme.Modules.restrictFunctor i).map (modulePullbackUnitIso f).hom ≫
      (Scheme.Modules.restrictUnitIso i).hom := by
  simp only [modulePullbackRestrictIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_hom, Iso.app_inv]
  rw [← restrictPullbackUnitIso j, Functor.map_comp, ← restrictPullbackUnitIso i]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  rw [modulePullbackUnitIso_comp_hom g j]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [modulePullbackUnitIso_congr, ← modulePullbackUnitIso_comp_hom i f]
  rw [← Category.assoc, ← Category.assoc,
    (Scheme.Modules.restrictFunctorIsoPullback i).hom.naturality]

end FLT.Mazur.FCurve
