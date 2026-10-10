/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedLinePullback

/-!
# Coherence of specified tensor-degree section pullbacks

Identity and composition hold for every section, by induction on tensor
powers and extensionality of sheaf tensor products on local pure tensors.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules

namespace FLT.Mazur.SectionGradedLinePullback

open FCurve ModuleLineBundleTensorPullback SectionGradedMultiplication

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] ModuleSheafTensor.tensor

variable {X Y Z : Scheme}

/-- The canonical identity comparison cancels the actual adjunction unit. -/
theorem lineMap_id (L : X.Modules) (U : X.Opens) (s : Γ(L, U)) :
    (lineMap (𝟙 X) ((pullbackId X).app L)).app U s = s := by
  have hh := unit_conjugateEquiv Adjunction.id
    (pullbackPushforwardAdjunction (𝟙 X)) (pullbackId X).hom L
  rw [conjugateEquiv_pullbackId_hom] at hh
  exact (congrArg (fun k ↦ k.app U s) hh).symm

/-- The actual identity pullback acts identically in every tensor degree as a sheaf map. -/
theorem powerMap_id (L : X.Modules) (n : ℕ) :
    powerMap (𝟙 X) ((pullbackId X).app L) n =
      (pushforwardId X).inv.app (tensorPower L n) := by
  induction n with
  | zero =>
    apply Scheme.Modules.hom_ext
    intro U
    ext r
    change sectionMap (𝟙 X) ((pullbackId X).app L) 0 U r = r
    rw [sectionMap_zero, Scheme.Hom.id_app]
    rfl
  | succ n ih =>
    apply ModuleSheafTensor.hom_ext
    intro U s t
    change sectionMap (𝟙 X) ((pullbackId X).app L) (n + 1) U (cons L n U s t) = _
    rw [sectionMap_cons, lineMap_id]
    have ht := congrArg (fun k ↦ k.app U t) ih
    change sectionMap (𝟙 X) ((pullbackId X).app L) n U t = t at ht
    rw [ht]
    rfl

/-- The identity comparison fixes each actual local tensor-degree section. -/
theorem sectionMap_id (L : X.Modules) (n : ℕ) (U : X.Opens) (s : Piece L U n) :
    sectionMap (𝟙 X) ((pullbackId X).app L) n U s = s :=
  congrArg (fun k ↦ k.app U s) (powerMap_id L n)

/-- The specified line comparison for two successive scheme maps. -/
def compIso (f : X ⟶ Y) (g : Y ⟶ Z) {L : Z.Modules} {M : Y.Modules} {N : X.Modules}
    (eg : (pullback g).obj L ≅ M) (ef : (pullback f).obj M ≅ N) :
    (pullback (f ≫ g)).obj L ≅ N :=
  ((pullbackComp f g).app L).symm ≪≫ (pullback f).mapIso eg ≪≫ ef

/-- The composite comparison gives the two successive actual line-section maps. -/
theorem lineMap_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    {L : Z.Modules} {M : Y.Modules} {N : X.Modules}
    (eg : (pullback g).obj L ≅ M) (ef : (pullback f).obj M ≅ N)
    (U : Z.Opens) (s : Γ(L, U)) :
    (lineMap (f ≫ g) (compIso f g eg ef)).app U s =
      (lineMap f ef).app (g ⁻¹ᵁ U) ((lineMap g eg).app U s) := by
  change ef.hom.app _ (((pullback f).map eg.hom).app _
    (((pullbackComp f g).inv.app L).app _
      (((pullbackPushforwardAdjunction (f ≫ g)).unit.app L).app U s))) = _
  rw [modulePullbackComp_inv_unit]
  have hn := congrArg (fun k ↦ k.app (g ⁻¹ᵁ U)
    (((pullbackPushforwardAdjunction g).unit.app L).app U s))
    ((pullbackPushforwardAdjunction f).unit.naturality eg.hom).symm
  exact congrArg (ef.hom.app (f ⁻¹ᵁ (g ⁻¹ᵁ U))) hn

/-- Tensor-degree sheaf maps satisfy composition with the actual pushforward compositor. -/
theorem powerMap_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    {L : Z.Modules} {M : Y.Modules} {N : X.Modules}
    (eg : (pullback g).obj L ≅ M) (ef : (pullback f).obj M ≅ N) (n : ℕ) :
    powerMap (f ≫ g) (compIso f g eg ef) n =
      powerMap g eg n ≫ (pushforward g).map (powerMap f ef n) ≫
        (pushforwardComp f g).hom.app (tensorPower N n) := by
  induction n with
  | zero =>
    apply Scheme.Modules.hom_ext
    intro U
    ext r
    change sectionMap (f ≫ g) (compIso f g eg ef) 0 U r =
      sectionMap f ef 0 (g ⁻¹ᵁ U) (sectionMap g eg 0 U r)
    rw [sectionMap_zero, sectionMap_zero, sectionMap_zero, Scheme.Hom.comp_app]
    rfl
  | succ n ih =>
    apply ModuleSheafTensor.hom_ext
    intro U s t
    change sectionMap (f ≫ g) (compIso f g eg ef) (n + 1) U (cons L n U s t) =
      sectionMap f ef (n + 1) (g ⁻¹ᵁ U) (sectionMap g eg (n + 1) U (cons L n U s t))
    rw [sectionMap_cons, sectionMap_cons, sectionMap_cons, lineMap_comp]
    exact congrArg (cons N n ((f ≫ g) ⁻¹ᵁ U)
      ((lineMap f ef).app (g ⁻¹ᵁ U) ((lineMap g eg).app U s)))
      (congrArg (fun k ↦ k.app U t) ih)

/-- Every local tensor-degree section obeys the actual composite pullback law. -/
theorem sectionMap_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    {L : Z.Modules} {M : Y.Modules} {N : X.Modules}
    (eg : (pullback g).obj L ≅ M) (ef : (pullback f).obj M ≅ N)
    (n : ℕ) (U : Z.Opens) (s : Piece L U n) :
    sectionMap (f ≫ g) (compIso f g eg ef) n U s =
      sectionMap f ef n (g ⁻¹ᵁ U) (sectionMap g eg n U s) :=
  congrArg (fun k ↦ k.app U s) (powerMap_comp f g eg ef n)

end FLT.Mazur.SectionGradedLinePullback
