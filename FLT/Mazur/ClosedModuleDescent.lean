/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineClosedModuleDescent
public import FLT.Mazur.CoherentClosedPushforward

/-!
# Foundations for descent along a closed immersion

Closed pushforward is faithful and reflects isomorphisms. The condition that
an ideal sheaf kills a module is invariant under isomorphism and is necessary
for descent. Over a Noetherian affine spectrum, the quotient construction
gives a coherent descent and characterizes the essential image on coherent
objects. Maps and isomorphisms between coherent affine closed pushforwards
lift uniquely. Global existence and fullness require further gluing results.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

namespace FLT.Mazur.FCurve.CoherentDevissage

variable {X Y : Scheme.{u}}

/-- Every open of a closed subscheme is the inverse image of an ambient open. -/
lemma closedImmersion_exists_preimage_open (f : X ⟶ Y) [IsClosedImmersion f]
    (U : X.Opens) : ∃ V : Y.Opens, f ⁻¹ᵁ V = U := by
  obtain ⟨V, hV, he⟩ := f.isClosedEmbedding.isInducing.isOpen_iff.mp U.isOpen
  exact ⟨⟨V, hV⟩, Opens.ext he⟩

/-- Closed pushforward detects equality of maps of actual module sheaves. -/
instance closedPushforward_faithful (f : X ⟶ Y) [IsClosedImmersion f] :
    (pushforward f).Faithful where
  map_injective {M N} a b h := by
    apply Scheme.Modules.hom_ext
    intro U
    obtain ⟨V, rfl⟩ := closedImmersion_exists_preimage_open f U
    exact congrArg (fun c ↦ c.app V) h

/-- Closed pushforward detects invertibility, without a coherence hypothesis. -/
instance closedPushforward_reflectsIsomorphisms (f : X ⟶ Y) [IsClosedImmersion f] :
    (pushforward f).ReflectsIsomorphisms where
  reflects {M N} a _ := by
    apply Hom.isIso_iff_isIso_app.mpr
    intro U
    obtain ⟨V, rfl⟩ := closedImmersion_exists_preimage_open f U
    exact inferInstanceAs (IsIso (((pushforward f).map a).app V))

/-- An ideal-sheaf datum kills the sections of a module on every affine open. -/
def IdealKilled (I : Y.IdealSheafData) (M : Y.Modules) : Prop :=
  ∀ (U : Y.affineOpens) (r : Γ(Y, U.1)), r ∈ I.ideal U →
    ∀ m : Γ(M, U.1), r • m = 0

/-- Annihilation by an ideal is preserved under a module-sheaf isomorphism. -/
lemma IdealKilled.of_iso {I : Y.IdealSheafData} {M N : Y.Modules}
    (hM : IdealKilled I M) (e : M ≅ N) : IdealKilled I N := by
  intro U r hr n
  have hn : e.hom.app U.1 (e.inv.app U.1 n) = n := by
    exact congrArg (fun c ↦ c n) (congrArg (fun c ↦ c.app U.1) e.inv_hom_id)
  rw [← hn, ← Hom.app_smul, hM U r hr, map_zero]

/-- The annihilation predicate depends only on the isomorphism class. -/
lemma idealKilled_iso_iff {I : Y.IdealSheafData} {M N : Y.Modules} (e : M ≅ N) :
    IdealKilled I M ↔ IdealKilled I N :=
  ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩

/-- Every pushforward from the prescribed closed subscheme is killed by its ideal. -/
theorem idealKilled_subschemePushforward (I : Y.IdealSheafData)
    (N : I.subscheme.Modules) : IdealKilled I ((pushforward I.subschemeι).obj N) :=
  subschemePushforward_ideal_smul I N

/-- Membership in the essential image implies the required affine annihilation. -/
theorem idealKilled_of_mem_essImage (I : Y.IdealSheafData) (M : Y.Modules)
    (hM : (pushforward I.subschemeι).essImage M) : IdealKilled I M := by
  obtain ⟨N, ⟨e⟩⟩ := hM
  exact (idealKilled_subschemePushforward I N).of_iso e

/-- A comparison lifting a fixed ambient map is unique whenever it exists. -/
theorem closedDescent_map_unique (f : X ⟶ Y) [IsClosedImmersion f]
    {N N' : X.Modules} {M M' : Y.Modules}
    (e : (pushforward f).obj N ≅ M) (e' : (pushforward f).obj N' ≅ M')
    (a : M ⟶ M') (b c : N ⟶ N')
    (hb : (pushforward f).map b ≫ e'.hom = e.hom ≫ a)
    (hc : (pushforward f).map c ≫ e'.hom = e.hom ≫ a) : b = c := by
  apply (pushforward f).map_injective
  exact (cancel_mono e'.hom).mp (hb.trans hc.symm)

/-- A lift of an ambient isomorphism is automatically an isomorphism. -/
theorem closedDescent_isIso (f : X ⟶ Y) [IsClosedImmersion f]
    {N N' : X.Modules} {M M' : Y.Modules}
    (e : (pushforward f).obj N ≅ M) (e' : (pushforward f).obj N' ≅ M')
    (a : M ≅ M') (b : N ⟶ N')
    (hb : (pushforward f).map b ≫ e'.hom = e.hom ≫ a.hom) : IsIso b := by
  have he : (pushforward f).map b = e.hom ≫ a.hom ≫ e'.inv := by
    rw [← Category.assoc, ← hb, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have : IsIso ((pushforward f).map b) := by rw [he]; infer_instance
  exact isIso_of_reflects_iso b (pushforward f)

/-- Affine global sections detect maps when the source is recovered by its tilde counit. -/
lemma affineSections_map_injective {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [IsIso M.fromTildeΓ] (a b : M ⟶ N)
    (h : moduleSpecΓFunctor.map a = moduleSpecΓFunctor.map b) : a = b := by
  apply (cancel_epi M.fromTildeΓ).mp
  exact (fromTildeΓNatTrans.naturality a).symm.trans
    ((congrArg (fun c ↦ (tilde.functor R).map c ≫ N.fromTildeΓ) h).trans
      (fromTildeΓNatTrans.naturality b))

/-- Maps of coherent affine closed pushforwards lift uniquely to the original sheaves. -/
theorem affineClosedPushforward_map_bijective {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (hφ : Function.Surjective φ.hom) (M N : (Spec S).Modules)
    [M.IsFinitePresentation] [N.IsFinitePresentation] :
    Function.Bijective
      ((pushforward (Spec.map φ)).map : (M ⟶ N) → _) := by
  have : IsClosedImmersion (Spec.map φ) := IsClosedImmersion.spec_of_surjective φ hφ
  refine ⟨(pushforward (Spec.map φ)).map_injective, ?_⟩
  intro a
  let eM := affinePushforwardSectionsIso φ M
  let eN := affinePushforwardSectionsIso φ N
  let g := eM.inv ≫ moduleSpecΓFunctor.map a ≫ eN.hom
  let g' : moduleSpecΓFunctor.obj M ⟶ moduleSpecΓFunctor.obj N :=
    ModuleCat.ofHom (X := moduleSpecΓFunctor.obj M) (Y := moduleSpecΓFunctor.obj N)
      { toFun := g.hom
        map_add' := map_add _
        map_smul' := fun s m ↦ by
          obtain ⟨r, rfl⟩ := hφ s
          exact g.hom.map_smul r m }
  let MQ : (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).FullSubcategory :=
    ⟨M, inferInstance⟩
  let NQ : (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).FullSubcategory :=
    ⟨N, inferInstance⟩
  obtain ⟨b, hb⟩ := (tildeEquiv (R := S)).inverse.map_surjective (X := MQ) (Y := NQ) g'
  refine ⟨b.hom, ?_⟩
  have := isIso_fromTildeΓ_pushforward φ M
  apply affineSections_map_injective
  apply (cancel_mono eN.hom).mp
  have hn : moduleSpecΓFunctor.map ((pushforward (Spec.map φ)).map b.hom) ≫ eN.hom =
      eM.hom ≫ (ModuleCat.restrictScalars φ.hom).map (moduleSpecΓFunctor.map b.hom) :=
    congrArg (fun c ↦ c.hom.app (op ⊤))
      ((pushforwardCompModulesSpecToSheafIso φ).hom.naturality b.hom)
  rw [hn]
  change moduleSpecΓFunctor.map b.hom = g' at hb
  rw [hb]
  have hg : (ModuleCat.restrictScalars φ.hom).map g' = g := by
    ext m
    rfl
  rw [hg]
  simp [g]

/-- An isomorphism of coherent affine closed pushforwards has exactly one descended lift. -/
theorem affineClosedPushforward_iso_unique {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (hφ : Function.Surjective φ.hom) (M N : (Spec S).Modules)
    [M.IsFinitePresentation] [N.IsFinitePresentation]
    (e : (pushforward (Spec.map φ)).obj M ≅ (pushforward (Spec.map φ)).obj N) :
    ∃! d : M ≅ N, (pushforward (Spec.map φ)).mapIso d = e := by
  have : IsClosedImmersion (Spec.map φ) := IsClosedImmersion.spec_of_surjective φ hφ
  obtain ⟨b, hb⟩ := (affineClosedPushforward_map_bijective φ hφ M N).surjective e.hom
  have : IsIso ((pushforward (Spec.map φ)).map b) := by rw [hb]; infer_instance
  have : IsIso b := isIso_of_reflects_iso b (pushforward (Spec.map φ))
  have he : (pushforward (Spec.map φ)).mapIso (asIso b) = e := Iso.ext hb
  exact ⟨asIso b, he, fun d hd ↦ (pushforward (Spec.map φ)).mapIso_injective
    (hd.trans he.symm)⟩

namespace AffineClosedModuleDescent

variable {R : CommRingCat.{u}} (I : Ideal R) (M : (Spec R).Modules)

/-- Annihilation of actual global sections is invariant under sheaf isomorphism. -/
lemma Killed.of_iso {I : Ideal R} {M N : (Spec R).Modules} (hM : Killed I M)
    (e : M ≅ N) :
    Killed I N := by
  let e' := (moduleSpecΓFunctor.mapIso e).toLinearEquiv
  intro r hr n
  obtain ⟨m, rfl⟩ := e'.surjective n
  rw [← e'.map_smul, hM r hr, map_zero]

/-- Every actual affine quotient pushforward has trivial ideal action on global sections. -/
theorem killed_pushforward (N : (Spec (.of (R ⧸ I))).Modules) :
    Killed I ((pushforward (immersion I)).obj N) := by
  let e := (affinePushforwardSectionsIso
    (CommRingCat.ofHom (Ideal.Quotient.mk I)) N).toLinearEquiv
  intro r hr m
  apply e.injective
  rw [e.map_smul, map_zero]
  change (Ideal.Quotient.mk I r) • e m = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_smul]

/-- The affine descent of a coherent sheaf is coherent over a Noetherian base. -/
theorem descent_isFinitePresentation [IsNoetherianRing R] [M.IsFinitePresentation]
    (hM : Killed I M) : (descent I M hM).IsFinitePresentation := by
  have : Module.Finite (R ⧸ I) (quotientSections I M hM) :=
    quotientSections_finite I M hM
  exact affineTilde_isFinitePresentation_of_finite _

/-- The affine construction supplies a coherent sheaf and its actual pushforward comparison. -/
theorem exists_coherent_descent [IsNoetherianRing R] [M.IsFinitePresentation]
    (hM : Killed I M) :
    ∃ N : (Spec (.of (R ⧸ I))).Modules,
      N.IsFinitePresentation ∧ Nonempty ((pushforward (immersion I)).obj N ≅ M) :=
  ⟨descent I M hM, descent_isFinitePresentation I M hM, ⟨pushforwardIso I M hM⟩⟩

/-- For a coherent affine sheaf, ideal annihilation exactly characterizes the essential image. -/
theorem killed_iff_mem_essImage [M.IsFinitePresentation] :
    Killed I M ↔ (pushforward (immersion I)).essImage M := by
  constructor
  · intro hM
    exact ⟨descent I M hM, ⟨pushforwardIso I M hM⟩⟩
  · rintro ⟨N, ⟨e⟩⟩
    exact (killed_pushforward I N).of_iso e

/-- Over a Noetherian ring the essential-image witness can itself be chosen coherent. -/
theorem killed_iff_exists_coherent_descent [IsNoetherianRing R] [M.IsFinitePresentation] :
    Killed I M ↔ ∃ N : (Spec (.of (R ⧸ I))).Modules,
      N.IsFinitePresentation ∧ Nonempty ((pushforward (immersion I)).obj N ≅ M) := by
  constructor
  · exact exists_coherent_descent I M
  · rintro ⟨N, _, ⟨e⟩⟩
    exact (killed_pushforward I N).of_iso e

end AffineClosedModuleDescent

end FLT.Mazur.FCurve.CoherentDevissage
