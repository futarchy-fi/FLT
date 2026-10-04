/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierIdealFinitePresentation
public import FLT.Mazur.CartierIdealStalkNeighborhood
public import FLT.Mazur.IdealModuleAffineTensor
public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.AlgebraicGeometry.Cover.Sigma
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Affine faithfully flat refinement and Cartier descent

A flat surjective open morphism admits a finite affine refinement over an
affine target. Its finite disjoint union is affine and faithfully flat.
Cartier pullback then descends finite presentation of the actual ideal;
regular stalk generators spread to Cartier neighborhoods.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X Y : Scheme.{u}} [IsAffine Y]

/-- Replace a flat surjective open map by a finite affine faithfully flat
refinement, preserving its actual Cartier ideal pullback. -/
theorem exists_affine_flat_surjective_cartier (I : Y.IdealSheafData) (f : X ⟶ Y)
    [Flat f] [Surjective f] (hf : IsOpenMap f)
    (hI : EffectiveCartier (I.comap f)) :
    ∃ (Z : Scheme.{u}) (_ : IsAffine Z) (g : Z ⟶ Y),
      Flat g ∧ Surjective g ∧ EffectiveCartier (I.comap g) := by
  let C := f.cover (P := @Flat) inferInstance
  let : QuasiCompactCover C.toPreZeroHypercover :=
    .of_isOpenMap (fun _ ↦ hf)
  obtain ⟨D, k, hfin, hk⟩ := QuasiCompactCover.exists_hom C
  let : Finite D.cover.I₀ := hfin
  have (i : D.cover.I₀) : IsAffine (D.cover.X i) := inferInstanceAs (IsAffine (Spec _))
  let g := Sigma.desc D.cover.f
  have hflat : Flat g := D.cover.sigma.map_prop default
  have hsurj : Surjective g := inferInstance
  refine ⟨∐ D.cover.X, inferInstance, g, hflat, hsurj, ?_⟩
  apply (effectiveCartier_iff_openCover _ (sigmaOpenCover D.cover.X)).mpr
  intro i
  have := hk i
  have hchart := hI.comap_of_isOpenImmersion (k.h₀ i)
  rw [← Scheme.IdealSheafData.comap_comp] at hchart ⊢
  have hki : k.h₀ i ≫ f = D.cover.f i := k.w₀ i
  simpa only [sigmaOpenCover_f, g, Sigma.ι_comp_desc, hki] using hchart

/-- Cartier ideals descend along flat surjective open maps with affine target. -/
theorem effectiveCartier_of_flat_surjective_open_affine (I : Y.IdealSheafData)
    (f : X ⟶ Y) [Flat f] [Surjective f] (hf : IsOpenMap f)
    (hI : EffectiveCartier (I.comap f)) : EffectiveCartier I := by
  obtain ⟨Z, hZ, g, hg, hs, hIg⟩ := exists_affine_flat_surjective_cartier I f hf hI
  let := hZ
  let := hg
  let := hs
  let := hIg.finitePresentation_sections
  let := idealModule_finitePresentation_of_flat_surjective I g
  let : Module.FinitePresentation Γ(Y, ⊤) (I.ideal ⟨⊤, isAffineOpen_top Y⟩) :=
    Module.FinitePresentation.of_equiv (idealModuleAffineEquiv I ⟨⊤, isAffineOpen_top Y⟩)
  intro y
  obtain ⟨r, hyr, hr⟩ := cartierChart_neighborhood_of_stalk I ⟨⊤, isAffineOpen_top Y⟩
    y trivial (stalk_generators_of_flat_surjective_comap I g hIg y)
  exact ⟨Y.affineBasicOpen (U := ⟨⊤, isAffineOpen_top Y⟩) r, hyr, hr⟩

end FLT.Mazur.FCurve
