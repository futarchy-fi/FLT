/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedPushforwardFull

/-!
# Quotient charts for closed module descent

The affine quotient construction is applied to the actual restrictions of the
ambient sheaf. Its output is transported to the inverse-image opens of the
prescribed closed subscheme, with the comparison to the ambient restriction.
On each fixed common ambient subopen, full faithfulness supplies transition
isomorphisms, their cocycle, and compatible maps of the constructed charts.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

namespace FLT.Mazur.FCurve.CoherentDevissage.ClosedDescentCharts

variable {Y : Scheme.{u}} (I : Y.IdealSheafData) (M : Y.Modules)

/-- The spectrum chart has precisely the original affine open as image. -/
lemma affineChart_image (U : Y.affineOpens) : U.2.fromSpec ''ᵁ ⊤ = U.1 := by
  rw [Scheme.Hom.image_top_eq_opensRange, U.2.opensRange_fromSpec]

/-- Scalars on the spectrum chart correspond to the original affine scalars. -/
lemma affineChart_scalars (U : Y.affineOpens) :
    (Scheme.ΓSpecIso Γ(Y, U.1)).inv ≫ (U.2.fromSpec.appIso ⊤).inv =
      Y.presheaf.map (eqToHom (affineChart_image U)).op := by
  apply (cancel_mono (U.2.fromSpec.appIso ⊤).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Scheme.Hom.appIso_hom]
  rw [← Category.assoc, U.2.fromSpec.naturality]
  rw [U.2.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  have he : (eqToHom U.2.fromSpec_preimage_self).op ≫
      ((Opens.map U.2.fromSpec.base).map (eqToHom (affineChart_image U))).op ≫
        (eqToHom (U.2.fromSpec.preimage_image_eq ⊤).symm).op = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [Category.assoc, ← Functor.map_comp]
  simp only [Quiver.Hom.unop_op]
  rw [he, CategoryTheory.Functor.map_id, Category.comp_id]

/-- Affine annihilation transports to the actual sheaf on the spectrum chart. -/
lemma affineRestriction_killed (hM : IdealKilled I M) (U : Y.affineOpens) :
    AffineClosedModuleDescent.Killed (I.ideal U) (M.restrict U.2.fromSpec) := by
  intro r hr s
  have hk := hM U r hr
  let e := M.presheaf.mapIso (eqToIso (affineChart_image U)).op
  obtain ⟨t, rfl⟩ := (ConcreteCategory.bijective_of_isIso e.hom).surjective s
  change ((U.2.fromSpec.appIso ⊤).inv ((Scheme.ΓSpecIso Γ(Y, U.1)).inv r)) •
      (M.presheaf.map (eqToHom (affineChart_image U)).op t) = 0
  have hs := congr($(affineChart_scalars U) r)
  simp only [CommRingCat.comp_apply] at hs
  rw [hs, ← Scheme.Modules.map_smul, hk t, map_zero]

/-- The descended quotient-spectrum sheaf uses the sections of the actual restriction. -/
abbrev quotient (hM : IdealKilled I M) (U : Y.affineOpens) :
    (Spec (.of (Γ(Y, U.1) ⧸ I.ideal U))).Modules :=
  AffineClosedModuleDescent.descent (I.ideal U) (M.restrict U.2.fromSpec)
    (affineRestriction_killed I M hM U)

/-- Identify the quotient spectrum with its actual open in the closed subscheme. -/
def chartIso (U : Y.affineOpens) :
    Spec (.of (Γ(Y, U.1) ⧸ I.ideal U)) ≅ (I.subschemeι ⁻¹ᵁ U.1).toScheme :=
  IsOpenImmersion.isoOfRangeEq (I.subschemeCover.f U) (I.subschemeι ⁻¹ᵁ U.1).ι
    (by rw [← Scheme.Hom.coe_opensRange, I.opensRange_subschemeCover_map,
      Scheme.Opens.range_ι])

@[reassoc (attr := simp)]
lemma chartIso_hom_ι (U : Y.affineOpens) :
    (chartIso I U).hom ≫ (I.subschemeι ⁻¹ᵁ U.1).ι = I.subschemeCover.f U :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The actual chart immersion agrees with the quotient immersion. -/
lemma chartIso_hom_restrict (U : Y.affineOpens) :
    (chartIso I U).hom ≫ (I.subschemeι ∣_ U.1) = I.glueDataObjι U := by
  rw [← cancel_mono U.1.ι, Category.assoc, morphismRestrict_ι,
    ← Category.assoc, chartIso_hom_ι, I.subschemeCover_map_subschemeι]

/-- The quotient module sheaf, now on the prescribed closed inverse-image open. -/
def chart (hM : IdealKilled I M) (U : Y.affineOpens) :
    (I.subschemeι ⁻¹ᵁ U.1).toScheme.Modules :=
  (pushforward (chartIso I U).hom).obj (quotient I M hM U)

/-- Transporting back from the spectrum chart recovers the ambient open restriction. -/
def affineRestrictionIso (U : Y.affineOpens) :
    (pushforward U.2.isoSpec.inv).obj (M.restrict U.2.fromSpec) ≅ M.restrict U.1.ι :=
  (pushforwardIsoRestrictInverse U.2.isoSpec.symm).app _ ≪≫
    (restrictFunctorComp U.2.isoSpec.hom U.2.fromSpec).symm.app M ≪≫
      (restrictFunctorCongr U.2.isoSpec_hom_fromSpec).app M

/-- The comparison on each ambient affine open uses the original coherent sheaf. -/
def comparison [M.IsFinitePresentation] (hM : IdealKilled I M) (U : Y.affineOpens) :
    (pushforward (I.subschemeι ∣_ U.1)).obj (chart I M hM U) ≅ M.restrict U.1.ι := by
  have hfin := coherentPresentation_restrict U.2.fromSpec M
  exact (pushforwardComp (chartIso I U).hom (I.subschemeι ∣_ U.1)).app _ ≪≫
    (pushforwardCongr (chartIso_hom_restrict I U)).app _ ≪≫
      (pushforwardComp (AffineClosedModuleDescent.immersion (I.ideal U))
        U.2.isoSpec.inv).symm.app _ ≪≫
      (pushforward U.2.isoSpec.inv).mapIso
        (AffineClosedModuleDescent.pushforwardIso (I.ideal U) (M.restrict U.2.fromSpec)
          (affineRestriction_killed I M hM U)) ≪≫ affineRestrictionIso M U

/-- The quotient chart is coherent in the locally Noetherian setting. -/
lemma quotient_isFinitePresentation [IsLocallyNoetherian Y] [M.IsFinitePresentation]
    (hM : IdealKilled I M) (U : Y.affineOpens) :
    (quotient I M hM U).IsFinitePresentation := by
  have hfin := coherentPresentation_restrict U.2.fromSpec M
  have hnoeth : IsNoetherianRing Γ(Y, U.1) :=
    IsLocallyNoetherian.component_noetherian U
  exact AffineClosedModuleDescent.descent_isFinitePresentation _ _ _

/-- Coherence survives transport to the actual closed chart. -/
lemma chart_isFinitePresentation [IsLocallyNoetherian Y] [M.IsFinitePresentation]
    (hM : IdealKilled I M) (U : Y.affineOpens) :
    (chart I M hM U).IsFinitePresentation := by
  have hfin := quotient_isFinitePresentation I M hM U
  exact coherentPresentation_pushforwardIso (chartIso I U) _

/-- The quotient scalars are exactly the scalars of the prescribed closed subscheme. -/
lemma quotient_scalar_image (U : Y.affineOpens) (r : Γ(Y, U.1)) :
    (I.subschemeObjIso U).hom (I.subschemeι.app U.1 r) = Ideal.Quotient.mk (I.ideal U) r := by
  have h : I.subschemeι.app U.1 ≫ (I.subschemeObjIso U).hom =
      CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U)) := by
    rw [I.subschemeι_app U, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congr($h r)

/-- The annihilation hypothesis uses the kernel of the actual closed inclusion. -/
lemma idealKilled_iff_kernel : IdealKilled I M ↔
    ∀ (U : Y.affineOpens) (r : Γ(Y, U.1)), I.subschemeι.app U.1 r = 0 →
      ∀ m : Γ(M, U.1), r • m = 0 := by
  simp only [IdealKilled, ← I.ker_subschemeι_app, RingHom.mem_ker]

/-- Extend a constructed chart sheaf to the whole closed subscheme. -/
abbrev chartExtension (hM : IdealKilled I M) (U : Y.affineOpens) : I.subscheme.Modules :=
  (pushforward (I.subschemeι ⁻¹ᵁ U.1).ι).obj (chart I M hM U)

/-- The chart extension agrees with the ambient sheaf on its ambient affine open. -/
def extensionComparison [M.IsFinitePresentation] (hM : IdealKilled I M)
    (U : Y.affineOpens) :
    ((pushforward I.subschemeι).obj (chartExtension I M hM U)).restrict U.1.ι ≅
      M.restrict U.1.ι :=
  (closedPushforwardRestriction I.subschemeι U.1).app _ ≪≫
    (pushforward (I.subschemeι ∣_ U.1)).mapIso
      ((restrictFunctorAdjCounitIso (I.subschemeι ⁻¹ᵁ U.1).ι).app _) ≪≫
    comparison I M hM U

/-- Compare a chart extension on any smaller ambient open, including nonaffine ones. -/
def subopenComparison [M.IsFinitePresentation] (hM : IdealKilled I M)
    (U : Y.affineOpens) (V : Y.Opens) (h : V ≤ U.1) :
    ((pushforward I.subschemeι).obj (chartExtension I M hM U)).restrict V.ι ≅
      M.restrict V.ι :=
  (restrictFunctorCongr (Y.homOfLE_ι h).symm).app _ ≪≫
    (restrictFunctorComp (Y.homOfLE h) U.1.ι).app _ ≪≫
    (restrictFunctor (Y.homOfLE h)).mapIso (extensionComparison I M hM U) ≪≫
    (restrictFunctorComp (Y.homOfLE h) U.1.ι).symm.app M ≪≫
    (restrictFunctorCongr (Y.homOfLE_ι h)).app M

/-- A closed chart restricted to the inverse image of an arbitrary ambient subopen. -/
abbrev chartOn (hM : IdealKilled I M) (U : Y.affineOpens) (V : Y.Opens) :
    (I.subschemeι ⁻¹ᵁ V).toScheme.Modules :=
  (chartExtension I M hM U).restrict (I.subschemeι ⁻¹ᵁ V).ι

/-- Open base change compares every restricted chart to the same ambient restriction. -/
def comparisonOn [M.IsFinitePresentation] (hM : IdealKilled I M)
    (U : Y.affineOpens) (V : Y.Opens) (h : V ≤ U.1) :
    (pushforward (I.subschemeι ∣_ V)).obj (chartOn I M hM U V) ≅ M.restrict V.ι :=
  ((closedPushforwardRestriction I.subschemeι V).app _).symm ≪≫
    subopenComparison I M hM U V h

/-- Lift the ambient identity to an isomorphism between charts on a common subopen. -/
def transitionOn [M.IsFinitePresentation] (hM : IdealKilled I M)
    (U U' : Y.affineOpens) (V : Y.Opens) (h : V ≤ U.1) (h' : V ≤ U'.1) :
    chartOn I M hM U V ≅ chartOn I M hM U' V :=
  (closedPushforwardFullyFaithful (I.subschemeι ∣_ V)).preimageIso
    (comparisonOn I M hM U V h ≪≫ (comparisonOn I M hM U' V h').symm)

/-- The lifted transition has precisely the prescribed ambient comparison. -/
lemma transitionOn_pushforward [M.IsFinitePresentation] (hM : IdealKilled I M)
    (U U' : Y.affineOpens) (V : Y.Opens) (h : V ≤ U.1) (h' : V ≤ U'.1) :
    (pushforward (I.subschemeι ∣_ V)).mapIso (transitionOn I M hM U U' V h h') =
      comparisonOn I M hM U V h ≪≫ (comparisonOn I M hM U' V h').symm :=
  (closedPushforwardFullyFaithful (I.subschemeι ∣_ V)).isoEquiv.apply_symm_apply _

/-- On a common ambient subopen, the lifted identity transitions satisfy the cocycle. -/
lemma transitionOn_cocycle [M.IsFinitePresentation] (hM : IdealKilled I M)
    (U₁ U₂ U₃ : Y.affineOpens) (V : Y.Opens)
    (h₁ : V ≤ U₁.1) (h₂ : V ≤ U₂.1) (h₃ : V ≤ U₃.1) :
    transitionOn I M hM U₁ U₂ V h₁ h₂ ≪≫ transitionOn I M hM U₂ U₃ V h₂ h₃ =
      transitionOn I M hM U₁ U₃ V h₁ h₃ := by
  apply (pushforward (I.subschemeι ∣_ V)).mapIso_injective
  simp only [Functor.mapIso_trans, transitionOn_pushforward]
  ext
  simp

/-- Identity transitions on a fixed common subopen. -/
lemma transitionOn_self [M.IsFinitePresentation] (hM : IdealKilled I M)
    (U : Y.affineOpens) (V : Y.Opens) (h : V ≤ U.1) :
    transitionOn I M hM U U V h h = Iso.refl _ := by
  apply (pushforward (I.subschemeι ∣_ V)).mapIso_injective
  simp [transitionOn_pushforward]

/-- The transition is the unique isomorphism recovering the ambient identity. -/
lemma transitionOn_unique [M.IsFinitePresentation] (hM : IdealKilled I M)
    (U U' : Y.affineOpens) (V : Y.Opens) (h : V ≤ U.1) (h' : V ≤ U'.1)
    (e : chartOn I M hM U V ≅ chartOn I M hM U' V)
    (he : (pushforward (I.subschemeι ∣_ V)).mapIso e =
      comparisonOn I M hM U V h ≪≫ (comparisonOn I M hM U' V h').symm) :
    e = transitionOn I M hM U U' V h h' :=
  (pushforward (I.subschemeι ∣_ V)).mapIso_injective
    (he.trans (transitionOn_pushforward I M hM U U' V h h').symm)

/-- The transition on the actual pairwise overlap, in the slice-site form used by gluing. -/
def overlap [M.IsFinitePresentation] (hM : IdealKilled I M) (U U' : Y.affineOpens) :
    (chartExtension I M hM U).over (I.subschemeι ⁻¹ᵁ U.1 ⊓ I.subschemeι ⁻¹ᵁ U'.1) ≅
      (chartExtension I M hM U').over (I.subschemeι ⁻¹ᵁ U.1 ⊓ I.subschemeι ⁻¹ᵁ U'.1) := by
  rw [← Scheme.Hom.preimage_inf]
  exact (overEquiv (I.subschemeι ⁻¹ᵁ (U.1 ⊓ U'.1))).fullyFaithfulFunctor.preimageIso
    ((overFunctorEquiv _).app _ ≪≫
      transitionOn I M hM U U' (U.1 ⊓ U'.1) inf_le_left inf_le_right ≪≫
        (overFunctorEquiv _).symm.app _)

variable {M} {N P : Y.Modules}

/-- Lift a map of the original sheaves to any constructed chart on a subopen. -/
def mapOn [M.IsFinitePresentation] [N.IsFinitePresentation]
    (hM : IdealKilled I M) (hN : IdealKilled I N) (a : M ⟶ N)
    (U : Y.affineOpens) (V : Y.Opens) (h : V ≤ U.1) :
    chartOn I M hM U V ⟶ chartOn I N hN U V :=
  (pushforward (I.subschemeι ∣_ V)).preimage
    ((comparisonOn I M hM U V h).hom ≫ (restrictFunctor V.ι).map a ≫
      (comparisonOn I N hN U V h).inv)

/-- The lifted map recovers the restriction of the supplied ambient map. -/
lemma mapOn_pushforward [M.IsFinitePresentation] [N.IsFinitePresentation]
    (hM : IdealKilled I M) (hN : IdealKilled I N) (a : M ⟶ N)
    (U : Y.affineOpens) (V : Y.Opens) (h : V ≤ U.1) :
    (pushforward (I.subschemeι ∣_ V)).map (mapOn I hM hN a U V h) =
      (comparisonOn I M hM U V h).hom ≫ (restrictFunctor V.ι).map a ≫
        (comparisonOn I N hN U V h).inv :=
  Functor.map_preimage _ _

/-- Chart maps preserve identities. -/
lemma mapOn_id [M.IsFinitePresentation] (hM : IdealKilled I M)
    (U : Y.affineOpens) (V : Y.Opens) (h : V ≤ U.1) :
    mapOn I hM hM (𝟙 M) U V h = 𝟙 _ := by
  apply (pushforward (I.subschemeι ∣_ V)).map_injective
  simp [mapOn_pushforward]

/-- Chart maps preserve composition. -/
lemma mapOn_comp [M.IsFinitePresentation] [N.IsFinitePresentation] [P.IsFinitePresentation]
    (hM : IdealKilled I M) (hN : IdealKilled I N) (hP : IdealKilled I P)
    (a : M ⟶ N) (b : N ⟶ P) (U : Y.affineOpens) (V : Y.Opens) (h : V ≤ U.1) :
    mapOn I hM hP (a ≫ b) U V h = mapOn I hM hN a U V h ≫ mapOn I hN hP b U V h := by
  apply (pushforward (I.subschemeι ∣_ V)).map_injective
  simp [mapOn_pushforward]

/-- On a common subopen, chart maps commute with the lifted identity transitions. -/
lemma mapOn_transition [M.IsFinitePresentation] [N.IsFinitePresentation]
    (hM : IdealKilled I M) (hN : IdealKilled I N) (a : M ⟶ N)
    (U U' : Y.affineOpens) (V : Y.Opens) (h : V ≤ U.1) (h' : V ≤ U'.1) :
    mapOn I hM hN a U V h ≫ (transitionOn I N hN U U' V h h').hom =
      (transitionOn I M hM U U' V h h').hom ≫ mapOn I hM hN a U' V h' := by
  apply (pushforward (I.subschemeι ∣_ V)).map_injective
  have ht (Q : Y.Modules) [Q.IsFinitePresentation] (hQ : IdealKilled I Q) :
      (pushforward (I.subschemeι ∣_ V)).map (transitionOn I Q hQ U U' V h h').hom =
        (comparisonOn I Q hQ U V h).hom ≫ (comparisonOn I Q hQ U' V h').inv :=
    congrArg Iso.hom (transitionOn_pushforward I Q hQ U U' V h h')
  simp only [Functor.map_comp, mapOn_pushforward, ht]
  simp

end FLT.Mazur.FCurve.CoherentDevissage.ClosedDescentCharts
