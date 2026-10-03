/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafTensorCurrying
public import FLT.Mazur.ProjectiveTwistTensor
public import FLT.Mazur.ModuleExactOpenCover
/-!
# Exactness of tensoring with a line sheaf

The sheafified tensor is additive and commutes with open restriction. On a
trivializing cover, tensoring with a line is isomorphic to the identity on
short complexes. Short exactness therefore descends from that cover.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve.ModuleLineTensorExact
open ModuleSheafTensor ModuleSheafTensorCurrying
variable {X Y : Scheme.{u}}
/-- Tensoring on the right is additive in module morphisms. -/
instance tensoring_additive (L : X.Modules) : (tensoring L).Additive where
  map_add {M N} f g := by
    apply ModuleSheafTensor.hom_ext
    intro U m l
    change (ModuleSheafTensor.map (f + g) (𝟙 L)).app U (pure M L U m l) = _
    simp only [map_pure, Hom.id_app, ConcreteCategory.id_apply]
    change pure N L U (f.app U m + g.app U m) l =
      (ModuleSheafTensor.map f (𝟙 L)).app U (pure M L U m l) +
      (ModuleSheafTensor.map g (𝟙 L)).app U (pure M L U m l)
    rw [map_pure, map_pure]
    exact congrArg (fun k ↦ k l) (((pairing N L).app U).map_add (f.app U m) (g.app U m))
/-- A line trivialization commutes with an arbitrary map in the other factor. -/
lemma trivial_natural {M N L : X.Modules} (e : L ≅ structureModule X) (f : M ⟶ N) :
    ModuleSheafTensor.map f (𝟙 L) ≫ (rightTrivialIso N e).hom =
      (rightTrivialIso M e).hom ≫ f := by
  apply ModuleSheafTensor.hom_ext
  intro U m l
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, map_pure, Hom.id_app,
    ConcreteCategory.id_apply, rightTrivialIso_pure]
  exact (f.val.app (op U)).hom.map_smul _ _ |>.symm
/-- The tensor restriction comparison is natural in the first factor. -/
lemma restrict_natural {M N L : X.Modules} (j : Y ⟶ X) [IsOpenImmersion j]
    (f : M ⟶ N) :
    (restrictFunctor j).map (ModuleSheafTensor.map f (𝟙 L)) ≫ (restrictIso N L j).hom =
      (restrictIso M L j).hom ≫
        ModuleSheafTensor.map ((restrictFunctor j).map f) (𝟙 (L.restrict j)) := by
  apply restrict_hom_ext j
  intro U m l
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, restrictIso_hom_pure,
    map_pure, Hom.id_app, ConcreteCategory.id_apply]
  change (restrictIso N L j).hom.app U
    (((tensor N L).restrictAppIso j U).inv
      ((ModuleSheafTensor.map f (𝟙 L)).app (j ''ᵁ U) (pure M L (j ''ᵁ U) m l))) = _
  rw [map_pure, restrictIso_hom_pure]
  rfl

/-- Restricting a tensorized short complex agrees with tensoring its restriction. -/
def restrictTensorIso (S : ShortComplex X.Modules) (L : X.Modules)
    (j : Y ⟶ X) [IsOpenImmersion j] :
    ((S.map (tensoring L)).map (restrictFunctor j)) ≅
      ((S.map (restrictFunctor j)).map (tensoring (L.restrict j))) :=
  ShortComplex.isoMk (restrictIso S.X₁ L j) (restrictIso S.X₂ L j)
    (restrictIso S.X₃ L j) (restrict_natural j S.f).symm (restrict_natural j S.g).symm

/-- Tensoring a short complex with a trivialized line gives the original complex. -/
def trivialTensorIso (S : ShortComplex X.Modules) {L : X.Modules}
    (e : L ≅ structureModule X) : S.map (tensoring L) ≅ S :=
  ShortComplex.isoMk (rightTrivialIso S.X₁ e) (rightTrivialIso S.X₂ e)
    (rightTrivialIso S.X₃ e) (trivial_natural e S.f).symm (trivial_natural e S.g).symm

/-- Tensoring with a locally free rank-one sheaf preserves short exactness. -/
lemma shortExact (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (L : X.Modules) (hL : LocallyFreeRankOne L) :
    (S.map (tensoring L)).ShortExact := by
  choose U hx e using hL
  apply FLT.Mazur.ModuleExactOpenCover.shortExact_of_cover U (fun x ↦ ⟨x, hx x⟩)
  intro x
  exact ShortComplex.shortExact_of_iso
    ((restrictTensorIso S L (U x).ι) ≪≫
      trivialTensorIso (S.map (restrictFunctor (U x).ι)) (e x).some).symm
    (hS.map_of_exact (restrictFunctor (U x).ι))
end FLT.Mazur.FCurve.ModuleLineTensorExact
