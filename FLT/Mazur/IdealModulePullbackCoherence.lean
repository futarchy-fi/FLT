/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealModulePullbackRestrict
public import FLT.Mazur.SheafPullbackPathComparison

/-!
# Coherence of the actual ideal-module pullback comparisons

Composition and equality of scheme maps preserve the actual inclusion into
the structure sheaf. Monicity of the full ideal inclusion then proves the
composition law for canonical comparisons to specified full ideals.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open SheafPullbackPathComparison
variable {X Y Z : Scheme.{u}}

/-- Iterated pullback of the ideal inclusion agrees with the composite scheme map. -/
lemma idealModulePullbackι_comp (I : Z.IdealSheafData) (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pullback f).map (idealModulePullbackι I g) ≫ (modulePullbackUnitIso f).hom =
      (pullbackComp f g).hom.app (idealModule I) ≫ idealModulePullbackι I (f ≫ g) := by
  simp only [idealModulePullbackι, Functor.map_comp, Category.assoc]
  rw [modulePullbackUnitIso_comp_hom]
  have hn := (pullbackComp f g).hom.naturality (idealModuleι I)
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (fun m ↦ m ≫ (modulePullbackUnitIso (f ≫ g)).hom) hn

/-- Normalization to an equal composite retains the original ideal inclusion. -/
lemma idealModulePullbackι_comparison (I : Z.IdealSheafData)
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (w : f ≫ g = k) :
    (pullback f).map (idealModulePullbackι I g) ≫ (modulePullbackUnitIso f).hom =
      (comparison f g k w).hom.app (idealModule I) ≫ idealModulePullbackι I k := by
  subst k
  simpa [comparison, pullbackCongr] using idealModulePullbackι_comp I f g

/-- Canonical comparisons to full ideals respect composition with its actual sheaf associator. -/
lemma idealModulePullbackIsoOfEq_comp (I : Z.IdealSheafData)
    (J : Y.IdealSheafData) (K : X.IdealSheafData)
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (w : f ≫ g = k)
    (hg : I.comap g = J) (hf : J.comap f = K) (hk : I.comap k = K)
    [IsIso (idealModulePullbackHom I g)] [IsIso (idealModulePullbackHom J f)]
    [IsIso (idealModulePullbackHom I k)] :
    (pullback f).map (idealModulePullbackIsoOfEq I g J hg).hom ≫
        (idealModulePullbackIsoOfEq J f K hf).hom =
      (comparison f g k w).hom.app (idealModule I) ≫
        (idealModulePullbackIsoOfEq I k K hk).hom := by
  apply (cancel_mono (idealModuleι K)).mp
  rw [Category.assoc, Category.assoc, idealModulePullbackIsoOfEq_ι,
    idealModulePullbackIsoOfEq_ι]
  dsimp only [idealModulePullbackι]
  rw [← Category.assoc, ← Functor.map_comp, idealModulePullbackIsoOfEq_ι]
  exact idealModulePullbackι_comparison I f g k w

end FLT.Mazur.FCurve
