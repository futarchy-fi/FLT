/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentRestriction

/-!
# Descent of finite local presentations along open covers

Finite presentations survive the iterated-slice equivalence in
`QuasicoherentData.bind`. The open/over equivalence then lets us assemble
finite local presentations on scheme restrictions into presentations on the
original scheme.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u v w

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace FLT.Mazur.FCurve

section Sites

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Shrinking the cover index leaves every finite presentation unchanged. -/
lemma coherentData_shrink_isFinite (M : SheafOfModules.{u} R)
    (q : M.QuasicoherentData) [q.IsFinitePresentation] :
    q.shrink.IsFinitePresentation :=
  ⟨fun i ↦ inferInstanceAs (q.presentation i.2.choose).IsFinite⟩

/-- Finite local presentation data with an arbitrary index yields local finite presentation. -/
lemma coherent_of_finiteData (M : SheafOfModules.{u} R)
    (q : M.QuasicoherentData) [q.IsFinitePresentation] : M.IsFinitePresentation :=
  ⟨q.shrink, coherentData_shrink_isFinite M q⟩

variable [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Binding a cover of finite local presentations preserves finiteness of both families. -/
lemma coherentData_bind_isFinite (M : SheafOfModules.{u} R) {I : Type u}
    (X : I → C) (hX : J.CoversTop X)
    (D : Π i, (M.over (X i)).QuasicoherentData) [∀ i, (D i).IsFinitePresentation] :
    (SheafOfModules.QuasicoherentData.bind M X hX D).IsFinitePresentation := by
  constructor
  rintro ⟨i, j⟩
  let e := SheafOfModules.pushforwardPushforwardEquivalence
    (Over.iteratedSliceEquiv ((D i).X j))
    (S := (R.over _).over _) (R := R.over _) (𝟙 _) (𝟙 _)
    (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)
  have : ((D i).presentation j).IsFinite := inferInstance
  have : (((D i).presentation j).map e.inverse (.refl _)).IsFinite :=
    affinePresentation_map_isFinite _ _ _
  exact inferInstanceAs
    ((((D i).presentation j).map e.inverse (.refl _)).ofIsIso _).IsFinite

/-- A cover on whose over sites the module is finitely presented descends the property. -/
lemma coherent_of_coversTop (M : SheafOfModules.{u} R) {I : Type u}
    (X : I → C) (hX : J.CoversTop X) [∀ i, (M.over (X i)).IsFinitePresentation] :
    M.IsFinitePresentation := by
  let D i := (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
    (M.over (X i))).choose
  have (i : I) : (D i).IsFinitePresentation :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (M.over (X i))).choose_spec
  have := coherentData_bind_isFinite M X hX D
  exact coherent_of_finiteData M (SheafOfModules.QuasicoherentData.bind M X hX D)

/-- Passing to an over site preserves finite local presentations. -/
lemma coherent_over [HasPullbacks C] [HasBinaryProducts C]
    (M : SheafOfModules.{u} R) (X : C) [M.IsFinitePresentation] :
    (M.over X).IsFinitePresentation :=
  coherent_pushforward_of_isLeftAdjoint (Over.forget X) (𝟙 (R.over X)) (Iso.refl _)

/-- Local finite presentation can be checked on any covering family of over sites. -/
theorem coherent_iff_coversTop [HasPullbacks C] [HasBinaryProducts C]
    (M : SheafOfModules.{u} R) {I : Type u} (X : I → C) (hX : J.CoversTop X) :
    M.IsFinitePresentation ↔ ∀ i, (M.over (X i)).IsFinitePresentation := by
  constructor
  · intro h i
    have := h
    exact coherent_over M (X i)
  · intro h
    have := h
    exact coherent_of_coversTop M X hX

end Sites

/-- Restricting from an over site to the open subspace preserves finite presentations. -/
lemma coherent_openEquiv_functor {X : TopCat.{u}} (U : Opens X)
    (R : X.Sheaf RingCat.{u}) (N : SheafOfModules.{u} (R.over U))
    [N.IsFinitePresentation] :
    ((U.sheafOfModulesEquivOver R).functor.obj N).IsFinitePresentation := by
  have : U.overEquivalence.inverse.PreservesOneHypercovers.{u}
      (Opens.grothendieckTopology ↥U) ((Opens.grothendieckTopology X).over U) :=
    Functor.PreservesOneHypercovers.of_coverPreserving
      (Functor.IsDenseSubsite.coverPreserving _ _ _)
  exact coherent_pushforward_of_isLeftAdjoint U.overEquivalence.inverse
    (U.overPullbackSheafEquivOver.app R).inv (U.sheafOfModulesEquivOverUnit R)

/-- Transport from an open subspace to its over site preserves finite presentations. -/
lemma coherent_openEquiv_inverse {X : TopCat.{u}} (U : Opens X)
    (R : X.Sheaf RingCat.{u}) (N : SheafOfModules.{u} (U.sheafRestrict.obj R))
    [N.IsFinitePresentation] :
    ((U.sheafOfModulesEquivOver R).inverse.obj N).IsFinitePresentation := by
  have : U.overEquivalence.functor.PreservesOneHypercovers.{u}
      ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology ↥U) :=
    Functor.PreservesOneHypercovers.of_coverPreserving
      (Functor.IsDenseSubsite.coverPreserving _ _ _)
  exact coherent_pushforward_of_isLeftAdjoint U.overEquivalence.functor
    (U.sheafRestrictSheafEquivOver.app R).inv (U.sheafOfModulesEquivOverInverseUnit R)

/-- The open-subspace transport also reflects finite local presentations.

The counit identifies the result of transporting in both directions with the
original sheaf; finiteness is invariant under that actual isomorphism. -/
theorem coherent_openEquiv_inverse_iff {X : TopCat.{u}} (U : Opens X)
    (R : X.Sheaf RingCat.{u}) (N : SheafOfModules.{u} (U.sheafRestrict.obj R)) :
    ((U.sheafOfModulesEquivOver R).inverse.obj N).IsFinitePresentation ↔
      N.IsFinitePresentation := by
  constructor
  · intro h
    have := h
    exact (SheafOfModules.isFinitePresentation (U.sheafRestrict.obj R)).prop_of_iso
      ((U.sheafOfModulesEquivOver R).counitIso.app N)
      (coherent_openEquiv_functor U R ((U.sheafOfModulesEquivOver R).inverse.obj N))
  · intro h
    have := h
    exact coherent_openEquiv_inverse U R N

open Scheme.Modules

/-- The inverse open/over equivalence preserves local finite presentations. -/
lemma coherent_overEquiv_inverse {X : Scheme.{u}} (U : X.Opens)
    (N : U.toScheme.Modules) [N.IsFinitePresentation] :
    ((overEquiv U).inverse.obj N).IsFinitePresentation :=
  coherent_openEquiv_inverse U X.ringCatSheaf N

/-- The forward open/over equivalence preserves local finite presentations. -/
lemma coherent_overEquiv_functor {X : Scheme.{u}} (U : X.Opens)
    (N : SheafOfModules.{u} (X.ringCatSheaf.over U)) [N.IsFinitePresentation] :
    ((overEquiv U).functor.obj N).IsFinitePresentation :=
  coherent_openEquiv_functor U X.ringCatSheaf N

/-- The open/over equivalence detects finite local presentation in both directions. -/
theorem coherent_overEquiv_iff {X : Scheme.{u}} (U : X.Opens)
    (N : SheafOfModules.{u} (X.ringCatSheaf.over U)) :
    ((overEquiv U).functor.obj N).IsFinitePresentation ↔ N.IsFinitePresentation := by
  constructor
  · intro h
    have := h
    exact (SheafOfModules.isFinitePresentation (X.ringCatSheaf.over U)).prop_of_iso
      ((overEquiv U).unitIso.app N).symm
      (coherent_overEquiv_inverse U ((overEquiv U).functor.obj N))
  · intro h
    have := h
    exact coherent_overEquiv_functor U N

/-- A finitely presented open restriction gives finite presentations on its over site. -/
lemma coherent_over_of_restrict {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    [(M.restrict U.ι).IsFinitePresentation] : (M.over U).IsFinitePresentation := by
  let e : (overEquiv U).inverse.obj (M.restrict U.ι) ≅ M.over U :=
    (overEquiv U).inverse.mapIso ((overFunctorEquiv U).app M).symm ≪≫
      ((overEquiv U).unitIso.app (M.over U)).symm
  exact (SheafOfModules.isFinitePresentation (X.ringCatSheaf.over U)).prop_of_iso e
    (coherent_overEquiv_inverse U (M.restrict U.ι))

/-- The concrete scheme restriction and the over-site restriction have the same property. -/
theorem coherent_over_iff_restrict {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    (M.over U).IsFinitePresentation ↔ (M.restrict U.ι).IsFinitePresentation := by
  constructor
  · intro h
    have := h
    exact (SheafOfModules.isFinitePresentation U.toScheme.ringCatSheaf).prop_of_iso
      ((overFunctorEquiv U).app M) (coherent_overEquiv_functor U (M.over U))
  · intro h
    have := h
    exact coherent_over_of_restrict M U

/-- Finite local presentations descend from an open cover indexed in the scheme universe. -/
theorem coherent_of_smallOpenCover {X : Scheme.{u}} (M : X.Modules) {I : Type u}
    (U : I → X.Opens) (hU : (⨆ i, U i) = ⊤)
    (hM : ∀ i, (M.restrict (U i).ι).IsFinitePresentation) : M.IsFinitePresentation := by
  have (i : I) : (M.over (U i)).IsFinitePresentation := by
    have := hM i
    exact coherent_over_of_restrict M (U i)
  apply coherent_of_coversTop M U
  rwa [Opens.coversTop_iff, IsOpenCover]

/-- Finite local presentations descend from an open cover of any index size. -/
theorem coherent_of_openCover {X : Scheme.{u}} (M : X.Modules) {I : Type v}
    (U : I → X.Opens) (hU : (⨆ i, U i) = ⊤)
    (hM : ∀ i, (M.restrict (U i).ι).IsFinitePresentation) : M.IsFinitePresentation := by
  let V : Set.range U → X.Opens := Subtype.val
  have hV : (⨆ i, V i) = ⊤ := by
    rw [← hU]
    apply le_antisymm
    · refine iSup_le fun i ↦ ?_
      change i.val ≤ _
      rw [← i.2.choose_spec]
      exact le_iSup U i.2.choose
    · exact iSup_le fun i ↦ le_iSup V ⟨U i, i, rfl⟩
  apply coherent_of_smallOpenCover M V hV
  rintro ⟨_, i, rfl⟩
  exact hM i

/-- The open-cover criterion for local finite presentation, with no finiteness of the cover. -/
theorem coherent_iff_openCover {X : Scheme.{u}} (M : X.Modules) {I : Type v}
    (U : I → X.Opens) (hU : (⨆ i, U i) = ⊤) :
    M.IsFinitePresentation ↔ ∀ i, (M.restrict (U i).ι).IsFinitePresentation := by
  constructor
  · intro h i
    have := h
    exact coherent_restrict (U i).ι M
  · exact coherent_of_openCover M U hU

/-- It suffices to give each point a neighborhood with finite local presentations. -/
theorem coherent_of_neighborhoods {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ (M.restrict U.ι).IsFinitePresentation) :
    M.IsFinitePresentation := by
  choose U hx hM using h
  apply coherent_of_openCover M U _ hM
  apply top_unique
  intro x _
  exact Opens.mem_iSup.mpr ⟨x, hx x⟩

/-- Local finite presentation is a neighborhood property at every point. -/
theorem coherent_iff_neighborhoods {X : Scheme.{u}} (M : X.Modules) :
    M.IsFinitePresentation ↔
      ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ (M.restrict U.ι).IsFinitePresentation := by
  constructor
  · intro h x
    have := h
    exact ⟨⊤, trivial, coherent_restrict (⊤ : X.Opens).ι M⟩
  · exact coherent_of_neighborhoods M

end FLT.Mazur.FCurve
