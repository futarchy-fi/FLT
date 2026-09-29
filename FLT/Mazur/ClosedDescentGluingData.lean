/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedDescentOverlapCoherence

/-!
# Effective gluing data for closed descent

Section evaluation connects the slice-site transitions to the canonical
restrictions on a common ambient open.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules
open FLT.Mazur.ModuleSheafMorphismGluing

universe u

namespace FLT.Mazur.FCurve.CoherentDevissage.ClosedDescentCharts

variable {X Y : Scheme.{u}}

/-- Conjugation by the slice-site comparison evaluates on image opens. -/
lemma overEquiv_map_app {P Q : X.Modules} (U : X.Opens)
    (a : P.over U ⟶ Q.over U) (T : U.toScheme.Opens) :
    (((overFunctorEquiv U).inv.app P ≫ (overEquiv U).functor.map a ≫
      (overFunctorEquiv U).hom.app Q).app T).hom =
        (localApp a (U.ι_image_le T)).toAddMonoidHom := by
  rfl

/-- The canonical lift of a restricted morphism to the slice site. -/
def sliceMap {P Q : X.Modules} (U : X.Opens)
    (a : P.restrict U.ι ⟶ Q.restrict U.ι) : P.over U ⟶ Q.over U :=
  (overEquiv U).fullyFaithfulFunctor.preimage
    ((overFunctorEquiv U).hom.app P ≫ a ≫ (overFunctorEquiv U).inv.app Q)

/-- The canonical lift has the prescribed map on every image subopen. -/
lemma sliceMap_app {P Q : X.Modules} (U : X.Opens)
    (a : P.restrict U.ι ⟶ Q.restrict U.ι) (T : U.toScheme.Opens) :
    (localApp (sliceMap U a) (U.ι_image_le T)).toAddMonoidHom = (a.app T).hom := by
  rw [← overEquiv_map_app]
  simp only [sliceMap, Functor.FullyFaithful.map_preimage, Category.assoc,
    Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- Restriction to the slice site agrees with the canonical geometric comparison. -/
lemma sliceMap_restrictionEquiv {P Q : X.Modules} (U : X.Opens)
    (a : P.restrict U.ι ⟶ Q.restrict U.ι) : restrictionEquiv U (sliceMap U a) = a := by
  apply Scheme.Modules.hom_ext
  intro T
  exact congrArg AddCommGrpCat.ofHom (sliceMap_app U a T)

/-- Evaluating a slice morphism commutes with equality of subopens. -/
lemma localApp_eqToHom {P Q : X.Modules} {U V W : X.Opens}
    (a : P.over U ⟶ Q.over U) (hV : V ≤ U) (hW : W ≤ U) (e : V = W) :
    P.presheaf.map (eqToHom e).op ≫
        AddCommGrpCat.ofHom (localApp a hV).toAddMonoidHom =
      AddCommGrpCat.ofHom (localApp a hW).toAddMonoidHom ≫
        Q.presheaf.map (eqToHom e).op := by
  subst W
  simp

/-- Slice evaluation of nested restriction is independent of the containing open. -/
lemma sliceMap_nested {P Q : X.Modules} {U V : X.Opens} (h : V ≤ U)
    (a : P.restrict U.ι ⟶ Q.restrict U.ι)
    (b : P.restrict V.ι ⟶ Q.restrict V.ι)
    (hab : (restrictFunctor (X.homOfLE h)).map a ≫
      (nestedRestriction h).hom.app Q = (nestedRestriction h).hom.app P ≫ b)
    (S : X.Opens) (hS : S ≤ V) :
    localApp (sliceMap U a) (hS.trans h) = localApp (sliceMap V b) hS := by
  obtain ⟨T, rfl⟩ : ∃ T : V.toScheme.Opens, V.ι ''ᵁ T = S :=
    ⟨V.ι ⁻¹ᵁ S, by simp [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hS]⟩
  apply LinearMap.toAddMonoidHom_injective
  rw [sliceMap_app]
  have hh := congrArg (fun f ↦ f.app T) hab
  simp only [Hom.comp_app, restrictMap_app, nestedRestriction_hom_app] at hh
  have e : V.ι ''ᵁ T = U.ι ''ᵁ (X.homOfLE h ''ᵁ T) := by
    simp only [← Scheme.Hom.comp_image, Scheme.homOfLE_ι]
  have hn := localApp_eqToHom (sliceMap U a) ((V.ι_image_le T).trans h)
    (U.ι_image_le _) e
  rw [sliceMap_app] at hn
  have he := hn.trans hh
  apply (cancel_epi (P.presheaf.map (eqToHom e).op)).mp at he
  exact congrArg AddCommGrpCat.Hom.hom he

/-- Transport of a slice morphism preserves its value on a fixed subopen. -/
lemma localApp_transport {P Q : X.Modules} {U V S : X.Opens}
    (e : U = V) (a : P.over U ⟶ Q.over U) (h : S ≤ U) (h' : S ≤ V) :
    localApp (e ▸ a) h' = localApp a h := by
  subst V
  rfl

/-- Equality transport also commutes with taking the forward map of an isomorphism. -/
lemma localApp_transportIso {P Q : X.Modules} {U V S : X.Opens}
    (e : U = V) (a : P.over U ≅ Q.over U) (h : S ≤ U) (h' : S ≤ V) :
    localApp (e ▸ a).hom h' = localApp a.hom h := by
  subst V
  rfl

/-- The slice lift preserves composition. -/
lemma sliceMap_comp {P Q R : X.Modules} (U : X.Opens)
    (a : P.restrict U.ι ⟶ Q.restrict U.ι)
    (b : Q.restrict U.ι ⟶ R.restrict U.ι) :
    sliceMap U (a ≫ b) = sliceMap U a ≫ sliceMap U b := by
  apply (overEquiv U).functor.map_injective
  simp only [sliceMap, Functor.map_comp, Functor.FullyFaithful.map_preimage]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

variable (I : Y.IdealSheafData) (M : Y.Modules) [M.IsFinitePresentation]
    (hM : IdealKilled I M)

/-- The overlap equality transport leaves its section map unchanged. -/
lemma overlap_localApp (U U' : Y.affineOpens) (S : I.subscheme.Opens)
    (h : S ≤ I.subschemeι ⁻¹ᵁ U.1 ⊓ I.subschemeι ⁻¹ᵁ U'.1) :
    localApp (overlap I M hM U U').hom h =
      localApp (sliceMap (I.subschemeι ⁻¹ᵁ (U.1 ⊓ U'.1))
        (transitionOn I M hM U U' (U.1 ⊓ U'.1) inf_le_left inf_le_right).hom)
          (by simpa only [Scheme.Hom.preimage_inf] using h) := by
  exact localApp_transportIso (I.subschemeι.preimage_inf (U := U.1) (V := U'.1))
    ((overEquiv _).fullyFaithfulFunctor.preimageIso
      ((overFunctorEquiv _).app _ ≪≫
        transitionOn I M hM U U' (U.1 ⊓ U'.1) inf_le_left inf_le_right ≪≫
          (overFunctorEquiv _).symm.app _)) _ h

/-- Every triple closed overlap is the inverse image of one common ambient open. -/
lemma tripleAmbient_preimage (U₁ U₂ U₃ : Y.affineOpens) (S : I.subscheme.Opens)
    (h₁ : S ≤ I.subschemeι ⁻¹ᵁ U₁.1) (h₂ : S ≤ I.subschemeι ⁻¹ᵁ U₂.1)
    (h₃ : S ≤ I.subschemeι ⁻¹ᵁ U₃.1) :
    I.subschemeι ⁻¹ᵁ ((closedAmbientOpen I.subschemeι).obj S ⊓ U₁.1 ⊓ U₂.1 ⊓ U₃.1) =
      S := by
  simp only [Scheme.Hom.preimage_inf, closedAmbientOpen_preimage,
    inf_eq_left.mpr h₁, inf_eq_left.mpr h₂, inf_eq_left.mpr h₃]

/-- Each original overlap transition agrees with the transition on a smaller ambient open. -/
lemma overlap_on_subopen (U U' : Y.affineOpens) (V : Y.Opens)
    (hV : V ≤ U.1) (hV' : V ≤ U'.1) (S : I.subscheme.Opens)
    (hS : S ≤ I.subschemeι ⁻¹ᵁ V) :
    localApp (overlap I M hM U U').hom
        (le_inf (hS.trans (I.subschemeι.preimage_mono hV))
          (hS.trans (I.subschemeι.preimage_mono hV'))) =
      localApp (sliceMap (I.subschemeι ⁻¹ᵁ V)
        (transitionOn I M hM U U' V hV hV').hom) hS := by
  rw [overlap_localApp]
  exact sliceMap_nested (I.subschemeι.preimage_mono (le_inf hV hV')) _ _
    (transitionOn_nested I M hM U U' (U.1 ⊓ U'.1) V inf_le_left inf_le_right
      (le_inf hV hV')) S hS

/-- The original slice-site overlap isomorphisms satisfy the gluing cocycle. -/
lemma overlap_cocycle (U₁ U₂ U₃ : Y.affineOpens) (S : I.subscheme.Opens)
    (h₁ : S ≤ I.subschemeι ⁻¹ᵁ U₁.1) (h₂ : S ≤ I.subschemeι ⁻¹ᵁ U₂.1)
    (h₃ : S ≤ I.subschemeι ⁻¹ᵁ U₃.1) (s : Γ(chartExtension I M hM U₁, S)) :
    localApp (overlap I M hM U₂ U₃).hom (le_inf h₂ h₃)
      (localApp (overlap I M hM U₁ U₂).hom (le_inf h₁ h₂) s) =
        localApp (overlap I M hM U₁ U₃).hom (le_inf h₁ h₃) s := by
  let V := (closedAmbientOpen I.subschemeι).obj S ⊓ U₁.1 ⊓ U₂.1 ⊓ U₃.1
  have hV₁ : V ≤ U₁.1 := inf_le_left.trans (inf_le_left.trans inf_le_right)
  have hV₂ : V ≤ U₂.1 := inf_le_left.trans inf_le_right
  have hV₃ : V ≤ U₃.1 := inf_le_right
  have hS : S ≤ I.subschemeι ⁻¹ᵁ V :=
    (tripleAmbient_preimage I U₁ U₂ U₃ S h₁ h₂ h₃).ge
  rw [overlap_on_subopen I M hM U₁ U₂ V hV₁ hV₂ S hS,
    overlap_on_subopen I M hM U₂ U₃ V hV₂ hV₃ S hS,
    overlap_on_subopen I M hM U₁ U₃ V hV₁ hV₃ S hS]
  have hc := congrArg Iso.hom (transitionOn_cocycle I M hM U₁ U₂ U₃ V hV₁ hV₂ hV₃)
  have hs := congrArg (sliceMap (I.subschemeι ⁻¹ᵁ V)) hc
  rw [Iso.trans_hom, sliceMap_comp] at hs
  exact congrArg (fun a ↦ localApp a hS s) hs

/-- Effective descent data uses the original quotient charts and overlap maps. -/
def gluingData : ModuleSheafGluing.Data (fun U : Y.affineOpens ↦ I.subschemeι ⁻¹ᵁ U.1) where
  obj := chart I M hM
  transition := overlap I M hM
  cocycle := overlap_cocycle I M hM

/-- The affine charts cover the prescribed closed subscheme. -/
lemma gluingData_cover : (⨆ U : Y.affineOpens, I.subschemeι ⁻¹ᵁ U.1) = ⊤ :=
  closedLiftChart_cover I.subschemeι

end FLT.Mazur.FCurve.CoherentDevissage.ClosedDescentCharts
