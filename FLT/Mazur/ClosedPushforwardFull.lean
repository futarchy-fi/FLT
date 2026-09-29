/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedModuleDescent
public import FLT.Mazur.ModuleSheafMorphismGluing

/-!
# Fullness of closed pushforward

The inducing map on spaces recovers an additive morphism from its pushforward.
Surjectivity on ambient affine opens makes this morphism locally linear.
Gluing the resulting local module maps gives full faithfulness for all module
sheaves, without coherence or finiteness assumptions.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules
open FLT.Mazur.ModuleSheafMorphismGluing

universe u

namespace FLT.Mazur.FCurve.CoherentDevissage

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]

/-- The maximal ambient open with a prescribed inverse image. -/
abbrev closedAmbientOpen : X.Opens ⥤ Y.Opens :=
  f.isClosedEmbedding.isInducing.functor

lemma closedAmbientOpen_preimage (U : X.Opens) :
    f ⁻¹ᵁ (closedAmbientOpen f).obj U = U :=
  f.isClosedEmbedding.isInducing.map_functorObj U

/-- Recover a presheaf after passing to ambient opens and taking inverse images. -/
def closedAdditiveRecovery (M : X.Modules) :
    (closedAmbientOpen f).op ⋙ ((pushforward f).obj M).presheaf ≅ M.presheaf :=
  NatIso.ofComponents (fun U ↦
    M.presheaf.mapIso (eqToIso (congrArg op (closedAmbientOpen_preimage f U.unop))))
    (fun g ↦ by
      dsimp
      rw [← M.presheaf.map_comp, ← M.presheaf.map_comp]
      congr 1)

variable {M N : X.Modules}

/-- Lift the underlying additive map using the inducing topology. -/
def closedAdditiveLift (a : (pushforward f).obj M ⟶ (pushforward f).obj N) :
    M.presheaf ⟶ N.presheaf :=
  (closedAdditiveRecovery f M).inv ≫
    Functor.whiskerLeft (closedAmbientOpen f).op a.mapPresheaf ≫
      (closedAdditiveRecovery f N).hom

/-- On each inverse-image open the additive lift recovers the supplied map. -/
lemma closedAdditiveLift_app (a : (pushforward f).obj M ⟶ (pushforward f).obj N)
    (V : Y.Opens) : (closedAdditiveLift f a).app (op (f ⁻¹ᵁ V)) = a.app V := by
  let h : V ⟶ (closedAmbientOpen f).obj (f ⁻¹ᵁ V) :=
    homOfLE (f.isClosedEmbedding.isInducing.le_functorObj_iff.mpr le_rfl)
  have hn := a.mapPresheaf.naturality h.op
  change M.presheaf.map ((Opens.map f.base).map h).op ≫ a.app V =
    a.app ((closedAmbientOpen f).obj (f ⁻¹ᵁ V)) ≫
      N.presheaf.map ((Opens.map f.base).map h).op at hn
  change (M.presheaf.map
    (eqToHom (congrArg op (closedAmbientOpen_preimage f (f ⁻¹ᵁ V))).symm) ≫
      a.app ((closedAmbientOpen f).obj (f ⁻¹ᵁ V))) ≫
    N.presheaf.map (eqToHom (congrArg op (closedAmbientOpen_preimage f (f ⁻¹ᵁ V)))) = _
  have he : eqToHom (congrArg op (closedAmbientOpen_preimage f (f ⁻¹ᵁ V))) =
      ((Opens.map f.base).map h).op := Subsingleton.elim _ _
  rw [Category.assoc, he, ← hn, ← Category.assoc, ← M.presheaf.map_comp]
  have hk : eqToHom (congrArg op (closedAmbientOpen_preimage f (f ⁻¹ᵁ V))).symm ≫
      ((Opens.map f.base).map h).op = 𝟙 _ := Subsingleton.elim _ _
  rw [hk, M.presheaf.map_id, Category.id_comp]

/-- Ambient affine inverse images form a basis on a closed subscheme. -/
lemma closedAffineBasis : Opens.IsBasis {W : X.Opens | ∃ V : Y.affineOpens, f ⁻¹ᵁ V.1 = W} := by
  convert Y.isBasis_affineOpens.of_isInducing f.isClosedEmbedding.isInducing using 1
  ext W
  constructor
  · rintro ⟨V, rfl⟩
    exact ⟨V.1, V.2, rfl⟩
  · rintro ⟨V, hV, rfl⟩
    exact ⟨⟨V, hV⟩, rfl⟩

/-- Scalar linearity is detected on the basis of ambient affine inverse images. -/
lemma closedAdditiveLift_smul (a : (pushforward f).obj M ⟶ (pushforward f).obj N)
    (U : X.Opens) (r : Γ(X, U)) (s : Γ(M, U)) :
    (closedAdditiveLift f a).app (op U) (r • s) =
      r • (closedAdditiveLift f a).app (op U) s := by
  let ι := {V : Y.affineOpens // f ⁻¹ᵁ V.1 ≤ U}
  let W : ι → X.Opens := fun V ↦ f ⁻¹ᵁ V.1.1
  have hc : U ≤ iSup W := by
    intro x hx
    obtain ⟨V, ⟨A, rfl⟩, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp (closedAffineBasis f) hx
    exact Opens.mem_iSup.mpr ⟨⟨A, hVU⟩, hxV⟩
  apply TopCat.Sheaf.eq_of_locally_eq' (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab X)
    W U (fun V ↦ homOfLE V.2) hc
  intro V
  have hn (t : Γ(M, U)) := congr($((closedAdditiveLift f a).naturality
    (homOfLE V.2).op) t)
  simp only [ConcreteCategory.comp_apply] at hn
  change N.presheaf.map (homOfLE V.2).op _ = N.presheaf.map (homOfLE V.2).op _
  rw [Scheme.Modules.map_smul, ← hn, ← hn, Scheme.Modules.map_smul,
    closedAdditiveLift_app]
  obtain ⟨b, hb⟩ := f.app_surjective V.1.1 V.1.2 (X.presheaf.map (homOfLE V.2).op r)
  rw [← hb]
  exact a.app_smul b _

/-- A chartwise module map, with linearity proved on its affine refinements. -/
def closedLiftChart (a : (pushforward f).obj M ⟶ (pushforward f).obj N)
    (U : X.Opens) : M.over U ⟶ N.over U :=
  ⟨PresheafOfModules.homMk
    (Functor.whiskerLeft (Over.forget U).op (closedAdditiveLift f a))
    (fun V r s ↦ closedAdditiveLift_smul f a V.unop.left r s)⟩

/-- All chart maps arise from the same additive map, so agree on actual overlaps. -/
lemma closedLiftChart_compatible (a : (pushforward f).obj M ⟶ (pushforward f).obj N) :
    Compatible (fun U : Y.affineOpens ↦ f ⁻¹ᵁ U.1)
      (fun U ↦ closedLiftChart f a (f ⁻¹ᵁ U.1)) := by
  intro i j V hi hj
  rfl

omit [IsClosedImmersion f] in
/-- Affine inverse images cover the closed subscheme. -/
lemma closedLiftChart_cover : (⨆ U : Y.affineOpens, f ⁻¹ᵁ U.1) = ⊤ := by
  rw [← f.preimage_iSup, iSup_affineOpens_eq_top, f.preimage_top]

/-- The preimage of any map of closed pushforwards, constructed by module-map gluing. -/
def closedPushforwardPreimage (a : (pushforward f).obj M ⟶ (pushforward f).obj N) :
    M ⟶ N :=
  glue (fun U : Y.affineOpens ↦ f ⁻¹ᵁ U.1) (closedLiftChart_cover f)
    (fun U ↦ closedLiftChart f a (f ⁻¹ᵁ U.1)) (closedLiftChart_compatible f a)

/-- Gluing retains the underlying additive lift. -/
lemma closedPushforwardPreimage_app
    (a : (pushforward f).obj M ⟶ (pushforward f).obj N) (U : X.Opens) :
    (closedPushforwardPreimage f a).app U = (closedAdditiveLift f a).app (op U) := by
  ext s
  apply section_ext (fun V : Y.affineOpens ↦ f ⁻¹ᵁ V.1) (closedLiftChart_cover f) U
  intro V
  change res N inf_le_left
    (glueSection _ (closedLiftChart_cover f) _ (closedLiftChart_compatible f a) U s) =
      res N inf_le_left ((closedAdditiveLift f a).app (op U) s)
  refine (res_glueSection (fun V : Y.affineOpens ↦ f ⁻¹ᵁ V.1)
    (closedLiftChart_cover f) (fun V ↦ closedLiftChart f a (f ⁻¹ᵁ V.1))
    (closedLiftChart_compatible f a) U s V).trans ?_
  exact congr($((closedAdditiveLift f a).naturality
    (homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ V.1 ≤ U)).op) s)

/-- The constructed preimage pushes forward to the original morphism. -/
@[simp]
lemma pushforward_closedPushforwardPreimage
    (a : (pushforward f).obj M ⟶ (pushforward f).obj N) :
    (pushforward f).map (closedPushforwardPreimage f a) = a := by
  apply Scheme.Modules.hom_ext
  intro U
  rw [pushforward_map_app, closedPushforwardPreimage_app, closedAdditiveLift_app]

/-- Closed pushforward is full on all module sheaves. -/
instance closedPushforward_full : (pushforward f).Full where
  map_surjective a := ⟨closedPushforwardPreimage f a, pushforward_closedPushforwardPreimage f a⟩

/-- Full faithfulness of closed pushforward, without finiteness hypotheses. -/
def closedPushforwardFullyFaithful : (pushforward f).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

/-- Every pushed-forward map has exactly one lift. -/
theorem closedPushforward_map_unique
    (a : (pushforward f).obj M ⟶ (pushforward f).obj N) :
    ∃! b : M ⟶ N, (pushforward f).map b = a :=
  ⟨closedPushforwardPreimage f a, pushforward_closedPushforwardPreimage f a,
    fun _b hb ↦ (pushforward f).map_injective
      (hb.trans (pushforward_closedPushforwardPreimage f a).symm)⟩

/-- Every isomorphism of actual closed pushforwards has a unique isomorphism lift. -/
theorem closedPushforward_iso_unique
    (e : (pushforward f).obj M ≅ (pushforward f).obj N) :
    ∃! d : M ≅ N, (pushforward f).mapIso d = e := by
  let d := (closedPushforwardFullyFaithful f).preimageIso e
  have hd : (pushforward f).mapIso d = e :=
    (closedPushforwardFullyFaithful f).isoEquiv.apply_symm_apply e
  exact ⟨d, hd, fun c hc ↦ (pushforward f).mapIso_injective (hc.trans hd.symm)⟩

end FLT.Mazur.FCurve.CoherentDevissage
