/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineChartMapLaws
public import FLT.Mazur.SchemeAffineOpenGluingMapRecovery

/-!
# Uniqueness and functor laws for the glued descent map

The affine base charts jointly detect maps. Their reconstruction equations
therefore characterize the glued map and prove identity and composition.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {ι : Type u}
variable (C : ι → Chart p) {M N P : Y.Modules}
variable (D : SchemeGeometricDescent.Data p M) (E : SchemeGeometricDescent.Data p N)
variable (F : SchemeGeometricDescent.Data p P)
variable [∀ i, ((pullback (C i).cover).obj M).IsQuasicoherent]
variable [∀ i, ((pullback (C i).cover).obj N).IsQuasicoherent]
variable [∀ i, ((pullback (C i).cover).obj P).IsQuasicoherent]
variable [∀ i, IsOpenImmersion (C i).base]
variable (hC : iSup (fun i ↦ (C i).base.opensRange) = ⊤)
attribute [local irreducible] Chart.sheaf Chart.map openGlued openGluedMap

/-- The original effective chart maps characterize their glued global morphism. -/
lemma openGluedMap_unique (f : M ⟶ N) (hf : D.MapCompatible p E f)
    (g : openGlued C D ⟶ openGlued C E)
    (hg : ∀ i, (pullback (C i).base).map g ≫ (openGluedChartIso C E i).hom =
      (openGluedChartIso C D i).hom ≫ (C i).map D E f hf) :
    g = openGluedMap C D E hC f hf := by
  apply ModuleSheafOpenImmersionGluing.hom_ext
    (fun i ↦ Spec (C i).baseRing) (fun i ↦ (C i).base)
  · intro x
    have hx : x ∈ iSup (fun i ↦ (C i).base.opensRange) := by rw [hC]; trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  · intro i
    apply (cancel_mono (openGluedChartIso C E i).hom).mp
    rw [hg, openGluedMap_chart]

/-- Gluing preserves the identity morphism. -/
lemma openGluedMap_identity (hf : D.MapCompatible p D (𝟙 M)) :
    openGluedMap C D D hC (𝟙 M) hf = 𝟙 _ := by
  symm
  apply openGluedMap_unique C D D hC (𝟙 M) hf
  intro i
  rw [Chart.map_identity, Category.comp_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- Gluing preserves composition of compatible original morphisms. -/
lemma openGluedMap_composition (f : M ⟶ N) (g : N ⟶ P)
    (hf : D.MapCompatible p E f) (hg : E.MapCompatible p F g)
    (hfg : D.MapCompatible p F (f ≫ g)) :
    openGluedMap C D F hC (f ≫ g) hfg =
      openGluedMap C D E hC f hf ≫ openGluedMap C E F hC g hg := by
  symm
  apply openGluedMap_unique C D F hC (f ≫ g) hfg
  intro i
  rw [Functor.map_comp, Category.assoc, openGluedMap_chart,
    ← Category.assoc, openGluedMap_chart, Category.assoc, Chart.map_composition]

end FLT.Mazur.SchemeAffineDescent
