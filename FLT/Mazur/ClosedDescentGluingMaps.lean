/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedDescentGluingData

/-!
# Compatible maps of closed descent charts

The open-immersion counit transports the lifted ambient morphism to each
original chart. Naturality and nested restriction identify its sections on
all subopens and prove compatibility with the original overlap transitions.
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

/-- The slice lift of a restricted global morphism is its original slice restriction. -/
lemma sliceMap_over {P Q : X.Modules} (U : X.Opens) (a : P ⟶ Q) :
    sliceMap U ((restrictFunctor U.ι).map a) = a.over U := by
  apply (restrictionEquiv U).injective
  rw [sliceMap_restrictionEquiv, restrictionEquiv_over]

variable (I : Y.IdealSheafData) {M N : Y.Modules}
    [M.IsFinitePresentation] [N.IsFinitePresentation]
    (hM : IdealKilled I M) (hN : IdealKilled I N) (a : M ⟶ N)

/-- Counit conjugation gives a morphism between the original quotient charts. -/
def chartMap (U : Y.affineOpens) : chart I M hM U ⟶ chart I N hN U :=
  (restrictFunctorAdjCounitIso (I.subschemeι ⁻¹ᵁ U.1).ι).inv.app _ ≫
    mapOn I hM hN a U U.1 le_rfl ≫
      (restrictFunctorAdjCounitIso (I.subschemeι ⁻¹ᵁ U.1).ι).hom.app _

/-- Counit naturality recovers the original lifted map after pushforward and restriction. -/
lemma chartMap_restrict (U : Y.affineOpens) :
    (restrictFunctor (I.subschemeι ⁻¹ᵁ U.1).ι).map
        ((pushforward (I.subschemeι ⁻¹ᵁ U.1).ι).map (chartMap I hM hN a U)) =
      mapOn I hM hN a U U.1 le_rfl := by
  apply (cancel_mono
    ((restrictFunctorAdjCounitIso (I.subschemeι ⁻¹ᵁ U.1).ι).hom.app _)).mp
  have hn := (restrictFunctorAdjCounitIso (I.subschemeι ⁻¹ᵁ U.1).ι).hom.naturality
    (chartMap I hM hN a U)
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [hn]
  change (restrictFunctorAdjCounitIso (I.subschemeι ⁻¹ᵁ U.1).ι).hom.app
      (chart I M hM U) ≫
    (restrictFunctorAdjCounitIso (I.subschemeι ⁻¹ᵁ U.1).ι).inv.app (chart I M hM U) ≫
      mapOn I hM hN a U U.1 le_rfl ≫
        (restrictFunctorAdjCounitIso (I.subschemeι ⁻¹ᵁ U.1).ι).hom.app (chart I N hN U) = _
  rw [Iso.hom_inv_id_app_assoc]

/-- The pushed-forward chart map restricts to the lifted map on every ambient subopen. -/
lemma chartMap_restrictOn (U : Y.affineOpens) (V : Y.Opens) (hV : V ≤ U.1) :
    (restrictFunctor (I.subschemeι ⁻¹ᵁ V).ι).map
        ((pushforward (I.subschemeι ⁻¹ᵁ U.1).ι).map (chartMap I hM hN a U)) =
      mapOn I hM hN a U V hV := by
  have hn := (nestedRestriction (I.subschemeι.preimage_mono hV)).hom.naturality
    ((pushforward (I.subschemeι ⁻¹ᵁ U.1).ι).map (chartMap I hM hN a U))
  simp only [Functor.comp_map] at hn
  rw [chartMap_restrict] at hn
  have hc := mapOn_nested I hM hN a U U.1 V le_rfl hV
  exact ((cancel_epi ((nestedRestriction (I.subschemeι.preimage_mono hV)).hom.app
    (chartExtension I M hM U))).mp (hc.symm.trans hn)).symm

/-- On every closed subopen, the chart map has precisely the lifted ambient section map. -/
lemma chartMap_pushforward_app (U : Y.affineOpens) (V : Y.Opens) (hV : V ≤ U.1)
    (S : I.subscheme.Opens) (hS : S ≤ I.subschemeι ⁻¹ᵁ V)
    (s : Γ(chartExtension I M hM U, S)) :
    ((pushforward (I.subschemeι ⁻¹ᵁ U.1).ι).map (chartMap I hM hN a U)).app S s =
      localApp (sliceMap (I.subschemeι ⁻¹ᵁ V) (mapOn I hM hN a U V hV)) hS s := by
  have ht := congrArg (sliceMap (I.subschemeι ⁻¹ᵁ V))
    (chartMap_restrictOn I hM hN a U V hV)
  rw [sliceMap_over] at ht
  exact congrArg (fun f ↦ localApp f hS s) ht

/-- Each closed subopen of an overlap has an ambient representative inside both charts. -/
lemma pairAmbient_preimage (U U' : Y.affineOpens) (S : I.subscheme.Opens)
    (h : S ≤ I.subschemeι ⁻¹ᵁ U.1) (h' : S ≤ I.subschemeι ⁻¹ᵁ U'.1) :
    I.subschemeι ⁻¹ᵁ ((closedAmbientOpen I.subschemeι).obj S ⊓ U.1 ⊓ U'.1) = S := by
  simp only [Scheme.Hom.preimage_inf, closedAmbientOpen_preimage,
    inf_eq_left.mpr h, inf_eq_left.mpr h']

/-- The actual chart morphisms intertwine the original slice-site overlap isomorphisms. -/
lemma chartMap_compatible (U U' : Y.affineOpens) (S : I.subscheme.Opens)
    (h : S ≤ I.subschemeι ⁻¹ᵁ U.1) (h' : S ≤ I.subschemeι ⁻¹ᵁ U'.1)
    (s : Γ(chartExtension I M hM U, S)) :
    localApp (overlap I N hN U U').hom (le_inf h h')
        (((pushforward (I.subschemeι ⁻¹ᵁ U.1).ι).map (chartMap I hM hN a U)).app S s) =
      ((pushforward (I.subschemeι ⁻¹ᵁ U'.1).ι).map (chartMap I hM hN a U')).app S
        (localApp (overlap I M hM U U').hom (le_inf h h') s) := by
  let V := (closedAmbientOpen I.subschemeι).obj S ⊓ U.1 ⊓ U'.1
  have hV : V ≤ U.1 := inf_le_left.trans inf_le_right
  have hV' : V ≤ U'.1 := inf_le_right
  have hS : S ≤ I.subschemeι ⁻¹ᵁ V := (pairAmbient_preimage I U U' S h h').ge
  rw [chartMap_pushforward_app I hM hN a U V hV S hS,
    chartMap_pushforward_app I hM hN a U' V hV' S hS,
    overlap_on_subopen I N hN U U' V hV hV' S hS,
    overlap_on_subopen I M hM U U' V hV hV' S hS]
  have hc := congrArg (sliceMap (I.subschemeι ⁻¹ᵁ V))
    (mapOn_transition I hM hN a U U' V hV hV')
  rw [sliceMap_comp, sliceMap_comp] at hc
  exact congrArg (fun f ↦ localApp f hS s) hc

/-- Every ambient morphism induces a compatible map of the constructed descent data. -/
def gluingMap : (gluingData I M hM).Map (gluingData I N hN) where
  app := chartMap I hM hN a
  compatible := chartMap_compatible I hM hN a

end FLT.Mazur.FCurve.CoherentDevissage.ClosedDescentCharts
