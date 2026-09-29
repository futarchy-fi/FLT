/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCoherent

/-!
# Restriction of locally finitely presented module sheaves

Finite local presentations transport along the same site functors as
quasi-coherent presentations. In particular they restrict along open immersions
of schemes, so the affine finiteness theorem applies to every affine chart.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe u v w v₂ w₂

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace FLT.Mazur.FCurve

section Sites

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  {D : Type v₂} [Category.{w₂} D] {K : GrothendieckTopology D}
  {S : Sheaf K RingCat.{u}}
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, HasSheafify (K.over X) AddCommGrpCat.{u}]
  [∀ X, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

variable (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
  (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R)

/-- Site pushforward preserves finite local presentations when its local functors
preserve colimits and the structure module. -/
lemma coherent_pushforward
    (η : (SheafOfModules.pushforward φ).obj (.unit R) ≅ .unit S)
    [∀ X, (Over.post (X := X) G).IsContinuous (K.over X) (J.over _)]
    (h : ∀ (X : D) (Y : C) (f : G.obj X ⟶ Y),
      PreservesColimitsOfSize.{u, u} <|
      SheafOfModules.pushforward.{u} (R := R.over Y)
        (F := Over.post (X := X) G ⋙ Over.map f)
        (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ))
    {M : SheafOfModules.{u} R} [M.IsFinitePresentation] :
    ((SheafOfModules.pushforward φ).obj M).IsFinitePresentation := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  let := hq
  let q' := q.pushforward G φ η h
  have hq' : q'.IsFinitePresentation := by
    constructor
    intro i
    let := h i.1 (q.X i.2.1) i.2.2
    exact affinePresentation_map_isFinite _ _ _
  refine ⟨q'.shrink, ⟨fun i ↦ ?_⟩⟩
  exact hq'.isFinite_presentation i.2.choose

/-- A left-adjoint restriction of sites with an invertible ring comparison
preserves finite local presentations. -/
lemma coherent_pushforward_of_isLeftAdjoint
    (η : (SheafOfModules.pushforward φ).obj (.unit R) ≅ .unit S)
    [G.IsLeftAdjoint] [IsIso φ]
    [∀ X, (Over.post (X := X) G).IsContinuous (K.over X) (J.over _)]
    [HasPullbacks C] [HasPullbacks D]
    {M : SheafOfModules.{u} R} [M.IsFinitePresentation] :
    ((SheafOfModules.pushforward φ).obj M).IsFinitePresentation := by
  apply +allowSynthFailures coherent_pushforward G φ η
  intro X Y f
  let G' := Over.post (X := X) G ⋙ Over.map f
  have : G'.IsContinuous (K.over X) (J.over Y) :=
    Functor.isContinuous_comp _ _ _ (J.over _) _
  have : G'.IsCocontinuous (K.over X) (J.over Y) :=
    isCocontinuous_comp _ _ _ (J.over _)
  let a : S.over X ⟶
      (G'.sheafPushforwardContinuous RingCat.{u} (K.over X) (J.over Y)).obj (R.over Y) :=
    ((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ
  have : (SheafOfModules.pushforward.{u} a).IsLeftAdjoint :=
    SheafOfModules.isLeftAdjoint_pushforward_of_isIso a
  infer_instance

end Sites

/-- Local finite presentation is preserved by restriction along an open immersion. -/
theorem coherent_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) [M.IsFinitePresentation] : (M.restrict f).IsFinitePresentation := by
  let α : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf :=
    { app U := (f.appIso U.unop).inv }
  have : IsIso α := NatIso.isIso_of_isIso_app _
  let φ : X.ringCatSheaf ⟶
      (f.opensFunctor.sheafPushforwardContinuous _ _ _).obj Y.ringCatSheaf :=
    ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩
  have : IsIso φ := by
    rw [← isIso_iff_of_reflects_iso _ (ObjectProperty.ι _)]
    dsimp [φ]
    infer_instance
  exact coherent_pushforward_of_isLeftAdjoint f.opensFunctor φ
    (Scheme.Modules.restrictUnitIso f)

/-- The actual sections of a coherent sheaf on any affine chart form a finite module. -/
theorem coherent_affineChart_finite {X : Scheme.{u}} {A : CommRingCat.{u}}
    (f : Spec A ⟶ X) [IsOpenImmersion f] (M : X.Modules) [M.IsFinitePresentation] :
    Module.Finite A Γ(M.restrict f, ⊤) := by
  have := coherent_restrict f M
  exact affineCoherent_finite_sections (M.restrict f)

/-- On an affine chart, a coherent sheaf is canonically tilde of its own sections. -/
def coherentAffineChartIso {X : Scheme.{u}} {A : CommRingCat.{u}}
    (f : Spec A ⟶ X) [IsOpenImmersion f] (M : X.Modules) [M.IsFinitePresentation] :
    M.restrict f ≅ tilde (moduleSpecΓFunctor.obj (M.restrict f)) := by
  have := coherent_restrict f M
  exact affineCoherentIso (M.restrict f)

end FLT.Mazur.FCurve
