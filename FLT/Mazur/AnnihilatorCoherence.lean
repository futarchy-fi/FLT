/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AnnihilatorSubsheaf

/-!
# Coherence of the canonical annihilator subsheaf

Affine chart sections retain the actual structure-ring action. Their canonical
inclusions identify restriction with localization of the coefficient annihilator.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.AnnihilatorSubsheaf

variable {X : Scheme.{u}} (I : X.IdealSheafData) (F : X.Modules)

/-- Every chart image lies in the chosen affine open. -/
lemma chart_image_le (U : X.affineOpens) (V : (Spec Γ(X, U.1)).Opens) :
    U.2.fromSpec ''ᵁ V ≤ U.1 := by
  exact (U.2.fromSpec.image_le_opensRange V).trans_eq U.2.opensRange_fromSpec

/-- Scalars on a spectrum chart are restrictions of the actual affine functions. -/
lemma chart_scalar (U : X.affineOpens) (V : (Spec Γ(X, U.1)).Opens)
    (r : Γ(X, U.1)) :
    (U.2.fromSpec.appIso V).inv
        ((Spec Γ(X, U.1)).presheaf.map V.leTop.op ((Scheme.ΓSpecIso _).inv r)) =
      X.presheaf.map (homOfLE (chart_image_le U V)).op r := by
  have hV : V ≤ U.2.fromSpec ⁻¹ᵁ U.1 := by simp
  have h := U.2.fromSpec.appLE_appIso_inv hV
  have he : U.2.fromSpec.appLE U.1 V hV =
      (Scheme.ΓSpecIso _).inv ≫ (Spec Γ(X, U.1)).presheaf.map V.leTop.op := by
    simp only [Scheme.Hom.appLE, U.2.fromSpec_app_self, Category.assoc,
      ← Functor.map_comp]
    rfl
  rw [he] at h
  exact congr($(h) r)

/-- Restriction to a chart preserves the original affine scalar action. -/
lemma chart_smul (U : X.affineOpens) (V : (Spec Γ(X, U.1)).Opens)
    (r : Γ(X, U.1)) (m : Γ(F.restrict U.2.fromSpec, V)) :
    (F.restrictAppIso U.2.fromSpec V).hom (r • m) =
      X.presheaf.map (homOfLE (chart_image_le U V)).op r •
        (F.restrictAppIso U.2.fromSpec V).hom m := by
  rw [smul_Spec_def, smul_restrictAppIso_hom_apply, chart_scalar]

/-- The chart inclusion is linear over the affine coordinate ring. -/
abbrev chartInclusionLinear (U : X.affineOpens) (V : (Spec Γ(X, U.1)).Opens) :
    Γ((sheaf I F).restrict U.2.fromSpec, V) →ₗ[Γ(X, U.1)]
      Γ(F.restrict U.2.fromSpec, V) :=
  ((modulesSpecToSheaf.map ((restrictFunctor U.2.fromSpec).map
    (inclusion I F))).hom.app (op V)).hom

/-- On affine chart opens, the actual inclusion has the expected annihilator image. -/
lemma chart_range (U : X.affineOpens) (V : (Spec Γ(X, U.1)).Opens)
    (hV : IsAffineOpen V) (m : Γ(F.restrict U.2.fromSpec, V)) :
    m ∈ Set.range (chartInclusionLinear I F U V) ↔
      m ∈ AffineAnnihilator.annihilated (I.ideal U) Γ(F.restrict U.2.fromSpec, V) := by
  let W : X.affineOpens := ⟨U.2.fromSpec ''ᵁ V,
    (U.2.fromSpec.isAffineOpen_iff_of_isOpenImmersion (U := V)).mpr hV⟩
  change m ∈ Set.range ((inclusion I F).app W.1) ↔ _
  rw [affine_range, ← I.map_ideal (show W ≤ U from chart_image_le U V)]
  change (show Γ(F, W.1) from m) ∈
    AffineAnnihilator.annihilated (Ideal.span _) Γ(F, W.1) ↔ _
  rw [AffineAnnihilator.mem_annihilated_span]
  constructor
  · intro h r hr
    have he := h _ ⟨r, hr, rfl⟩
    exact (chart_smul F U V r m).trans he
  · intro h r hr
    obtain ⟨a, ha, rfl⟩ := hr
    exact (chart_smul F U V a m).symm.trans (h a ha)

/-- The chart comparison uses precisely the original section inclusion. -/
def chartSectionsEquiv (U : X.affineOpens) (V : (Spec Γ(X, U.1)).Opens)
    (hV : IsAffineOpen V) :
    Γ((sheaf I F).restrict U.2.fromSpec, V) ≃ₗ[Γ(X, U.1)]
      AffineAnnihilator.annihilated (I.ideal U) Γ(F.restrict U.2.fromSpec, V) :=
  LinearEquiv.ofBijective
    ((chartInclusionLinear I F U V).codRestrict _
      (fun m ↦ (chart_range I F U V hV _).mp ⟨m, rfl⟩))
    ⟨fun _ _ h ↦ ModuleSubobjectCoverEquality.app_injective (inclusion I F)
        (U.2.fromSpec ''ᵁ V) (congrArg Subtype.val h),
      fun m ↦ by
        obtain ⟨n, hn⟩ := (chart_range I F U V hV m.val).mpr m.property
        exact ⟨n, Subtype.ext hn⟩⟩

@[simp]
lemma chartSectionsEquiv_val (U : X.affineOpens) (V : (Spec Γ(X, U.1)).Opens)
    (hV : IsAffineOpen V) (m : Γ((sheaf I F).restrict U.2.fromSpec, V)) :
    (chartSectionsEquiv I F U V hV m).val = chartInclusionLinear I F U V m := rfl

/-- The canonical section inclusions commute with the actual chart restrictions. -/
lemma chartInclusionLinear_restrict (U : X.affineOpens)
    {V W : (Spec Γ(X, U.1)).Opens} (h : W ≤ V)
    (m : Γ((sheaf I F).restrict U.2.fromSpec, V)) :
    chartInclusionLinear I F U W
        (((sheaf I F).restrict U.2.fromSpec).presheaf.map (homOfLE h).op m) =
      (F.restrict U.2.fromSpec).presheaf.map (homOfLE h).op
        (chartInclusionLinear I F U V m) := by
  exact congr($(((restrictFunctor U.2.fromSpec).map
    (inclusion I F)).mapPresheaf.naturality (homOfLE h).op) m)

/-- Principal restriction of the actual annihilator sections is localization. -/
theorem chart_isLocalizing [IsLocallyNoetherian X] [F.IsFinitePresentation]
    (U : X.affineOpens) :
    IsLocalizing (modulesSpecToSheaf.obj ((sheaf I F).restrict U.2.fromSpec)) := by
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have : (F.restrict U.2.fromSpec).IsFinitePresentation :=
    CoherentDevissage.coherentPresentation_restrict _ F
  intro r
  let M := F.restrict U.2.fromSpec
  let K := (sheaf I F).restrict U.2.fromSpec
  let f := PrincipalSubmoduleCoordinates.toSections M r
  let i := chartInclusionLinear I F U ⊤
  let j := chartInclusionLinear I F U (PrimeSpectrum.basicOpen r)
  have hi : Function.Injective i :=
    ModuleSubobjectCoverEquality.app_injective (inclusion I F) _
  have hj : Function.Injective j :=
    ModuleSubobjectCoverEquality.app_injective (inclusion I F) _
  have hn (m : Γ(K, ⊤)) :
      j (PrincipalSubmoduleCoordinates.toSections K r m) = f (i m) :=
    chartInclusionLinear_restrict I F U le_top m
  refine ⟨?_, ?_, ?_⟩
  · intro t
    obtain ⟨n, hn⟩ := t.property
    change IsUnit (algebraMap Γ(X, U.1)
      (Module.End Γ(X, U.1) Γ(K, PrimeSpectrum.basicOpen r)) t.val)
    rw [← hn]
    simpa only [map_pow] using
      (K.isUnit_algebraMap_end_of_le_basicOpen r le_rfl).pow n
  · intro y
    have hy := (chart_range I F U _ (IsAffineOpen.Spec_basicOpen r) (j y)).mp ⟨y, rfl⟩
    let A := Γ(Spec Γ(X, U.1), PrimeSpectrum.basicOpen r)
    have hy' := (AffineAnnihilator.mem_annihilated_map (I.ideal U) A (j y)).mpr hy
    rw [← AffineAnnihilator.localized_annihilated_map (I.ideal U)
      (IsNoetherian.noetherian _) (.powers r) A f] at hy'
    obtain ⟨m, hm, t, ht⟩ := hy'
    obtain ⟨x, hx⟩ := (chart_range I F U ⊤ (isAffineOpen_top _) m).mpr hm
    refine ⟨⟨x, t⟩, hj ?_⟩
    change j (t.val • y) = j (PrincipalSubmoduleCoordinates.toSections K r x)
    rw [j.map_smul, hn, hx, ← ht]
    exact IsLocalizedModule.mk'_cancel' f m t
  · intro x y h
    have he : f (i x) = f (i y) := (hn x).symm.trans ((congrArg j h).trans (hn y))
    obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := .powers r) (f := f) he
    refine ⟨t, hi ?_⟩
    exact (i.map_smul t.val x).trans (ht.trans (i.map_smul t.val y).symm)

/-- The affine counit identifies the actual kernel restriction with its tilde. -/
instance chart_fromTildeΓ_isIso [IsLocallyNoetherian X] [F.IsFinitePresentation]
    (U : X.affineOpens) : IsIso ((sheaf I F).restrict U.2.fromSpec).fromTildeΓ :=
  (isIso_fromTildeΓ_iff_isLocalizing _).mpr (chart_isLocalizing I F U)

/-- The affine restriction is the tilde of A1's actual coefficient annihilator. -/
def chartIso [IsLocallyNoetherian X] [F.IsFinitePresentation] (U : X.affineOpens) :
    AffineAnnihilator.sheaf (I.ideal U) (F.restrict U.2.fromSpec) ≅
      (sheaf I F).restrict U.2.fromSpec :=
  (tilde.functor Γ(X, U.1)).mapIso
    (chartSectionsEquiv I F U ⊤ (isAffineOpen_top _)).symm.toModuleIso ≪≫
      asIso ((sheaf I F).restrict U.2.fromSpec).fromTildeΓ

/-- The tilde comparison preserves the inclusion in the original restricted sheaf. -/
lemma chartIso_inclusion [IsLocallyNoetherian X] [F.IsFinitePresentation]
    (U : X.affineOpens) :
    (chartIso I F U).hom ≫ (restrictFunctor U.2.fromSpec).map (inclusion I F) =
      AffineAnnihilator.inclusion (I.ideal U) (F.restrict U.2.fromSpec) := by
  let a := (restrictFunctor U.2.fromSpec).map (inclusion I F)
  have hn : (tilde.functor Γ(X, U.1)).map (moduleSpecΓFunctor.map a) ≫
      (F.restrict U.2.fromSpec).fromTildeΓ =
        ((sheaf I F).restrict U.2.fromSpec).fromTildeΓ ≫ a :=
    fromTildeΓNatTrans.naturality a
  dsimp only [chartIso, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
  rw [Category.assoc, ← hn, ← Functor.map_comp_assoc]
  change (tilde.functor Γ(X, U.1)).map _ ≫ _ =
    (tilde.functor Γ(X, U.1)).map _ ≫ _
  congr 1
  congr 1
  ext m
  exact congrArg Subtype.val
    ((chartSectionsEquiv I F U ⊤ (isAffineOpen_top _)).apply_symm_apply m)

/-- The globally constructed annihilator subsheaf is coherent. -/
theorem sheaf_coherent [IsLocallyNoetherian X] [F.IsFinitePresentation] :
    (sheaf I F).IsFinitePresentation := by
  apply CoherentDevissage.coherentPresentation_of_affine_restrict
  intro U
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have : (F.restrict U.2.fromSpec).IsFinitePresentation :=
    CoherentDevissage.coherentPresentation_restrict _ F
  exact (SheafOfModules.isFinitePresentation (Spec Γ(X, U.1)).ringCatSheaf).prop_of_iso
    (chartIso I F U) (AffineAnnihilator.sheaf_coherent _ _)

end FLT.Mazur.AnnihilatorSubsheaf
