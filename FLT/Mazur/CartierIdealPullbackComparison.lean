/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealModulePrincipalPullback
public import FLT.Mazur.RelativeCartierIdealPullback
public import FLT.Mazur.LocalCartierGeneratorDescent
public import FLT.Mazur.DivisorLinePullback

/-!
# Pullback comparison when the pulled-back divisor is Cartier

If both the original ideal and its comap are effective Cartier, the canonical
ideal-module comparison is invertible. The scheme morphism need not be flat.
Duality gives the corresponding comparison for the actual divisor line.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

variable {X Y : Scheme.{u}} {I : Y.IdealSheafData}

/-- A Cartier comap makes the canonical ideal comparison invertible, without flatness. -/
theorem idealModulePullbackHom_isIso_of_cartier (f : X ⟶ Y)
    (hI : EffectiveCartier I) (hJ : EffectiveCartier (I.comap f)) :
    IsIso (idealModulePullbackHom I f) := by
  choose U hxU hU using fun x : X ↦ hI (f x)
  choose V hxV hVU hV using fun x : X ↦
    hJ.exists_chart_le (show x ∈ f ⁻¹ᵁ (U x).1 from hxU x)
  apply ModuleSheafOpenIsoDetection.isIso_of_openCover _ (fun x ↦ (V x).1)
    (fun x ↦ ⟨x, hxV x⟩)
  intro x
  let g := f.resLE (U x).1 (V x).1 (hVU x)
  have : IsAffine (U x).1.toScheme := (U x).2
  have : IsAffine (V x).1.toScheme := (V x).2
  obtain ⟨a, ha, hIa⟩ := CartierChart.comap_ι_top (hU x)
  have hEq : (I.comap (U x).1.ι).comap g = (I.comap f).comap (V x).1.ι := by
    rw [← Scheme.IdealSheafData.comap_comp, f.resLE_comp_ι (hVU x),
      Scheme.IdealSheafData.comap_comp]
  have hJ' : CartierChart ((I.comap (U x).1.ι).comap g)
      ⟨⊤, isAffineOpen_top (V x).1.toScheme⟩ := hEq ▸ CartierChart.comap_ι_top (hV x)
  obtain ⟨b, hb, hJb⟩ := hJ'
  have hJa : ((I.comap (U x).1.ι).comap g).ideal
      ⟨⊤, isAffineOpen_top (V x).1.toScheme⟩ = Ideal.span {g.appTop a} := by
    rw [Scheme.IdealSheafData.ideal_comap_top, hIa, Ideal.map_span, Set.image_singleton]
  have hg : IsRegular (g.appTop a) := isRegular_of_mem_span_singleton hb (by
    rw [← hJa, hJb]
    exact Ideal.subset_span (Set.mem_singleton b))
  have := idealModulePullbackHom_isIso_principal (I.comap (U x).1.ι) g a ha hIa hg
  exact idealModulePullbackHom_isIso_restrict I f g (V x).1.ι (U x).1.ι
    (f.resLE_comp_ι (hVU x)).symm

/-- The actual divisor lines commute with every morphism for which the comap stays Cartier. -/
def divisorLinePullbackIsoOfCartier (f : X ⟶ Y) (hI : EffectiveCartier I)
    (hJ : EffectiveCartier (I.comap f)) :
    (pullback f).obj (divisorLineBundle I hI) ≅ divisorLineBundle (I.comap f) hJ := by
  have := idealModulePullbackHom_isIso_of_cartier f hI hJ
  exact divisorLinePullbackIsoOfEq f hI hJ rfl

/-- This comparison preserves the canonical divisor section map. -/
@[reassoc]
lemma divisorLinePullbackIsoOfCartier_section (f : X ⟶ Y) (hI : EffectiveCartier I)
    (hJ : EffectiveCartier (I.comap f)) :
    (pullback f).map (divisorSectionMap hI) ≫
        (divisorLinePullbackIsoOfCartier f hI hJ).hom =
      (modulePullbackUnitIso f).hom ≫ divisorSectionMap hJ := by
  have := idealModulePullbackHom_isIso_of_cartier f hI hJ
  exact divisorLinePullbackIsoOfEq_section f hI hJ rfl

end FLT.Mazur.FCurve
