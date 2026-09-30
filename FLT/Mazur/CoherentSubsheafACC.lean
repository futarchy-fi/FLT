/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentAffineCoverSections
public import FLT.Mazur.CoherentSubmoduleExtension
public import FLT.Mazur.ModuleSheafOpenIsoDetection

/-!
# Ascending chains of coherent subsheaves

Images on sections of a finite affine cover form ascending chains in finite
modules over Noetherian rings. Their simultaneous stabilization implies equality
of the original subsheaves, by affine reconstruction and open-cover detection.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.FCurve.CoherentDevissage
open FLT.Mazur.CoherentSubmoduleEnlargement FLT.Mazur.ModuleSubobjectCoverEquality

universe u

namespace FLT.Mazur.CoherentSubsheafACC

/-- Affine reconstruction detects isomorphisms from the actual section map. -/
lemma affine_isIso_of_sections {R : CommRingCat.{u}} {L N : (Spec R).Modules}
    [L.IsFinitePresentation] [N.IsFinitePresentation] (f : L ⟶ N)
    (hf : Function.Bijective ((moduleSpecΓFunctor.map f).hom)) : IsIso f := by
  have : IsIso (moduleSpecΓFunctor.map f) := (ConcreteCategory.isIso_iff_bijective _).mpr hf
  have he : f = inv L.fromTildeΓ ≫
      (tilde.functor R).map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ := by
    have hn := fromTildeΓNatTrans.naturality f
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    change (tilde.functor R).map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ =
      L.fromTildeΓ ≫ f at hn
    rw [hn, IsIso.inv_hom_id_assoc]
  rw [he]
  infer_instance

variable {X : Scheme.{u}} {L N M : X.Modules}

/-- On an affine open, bijectivity on sections implies invertibility on the open. -/
lemma isIso_restrict_of_affine_sections [L.IsFinitePresentation] [N.IsFinitePresentation]
    (f : L ⟶ N) {U : X.Opens} (hU : IsAffineOpen U)
    (hf : Function.Bijective (f.app U)) : IsIso ((restrictFunctor U.ι).map f) := by
  let j := hU.fromSpec
  have := coherentPresentation_restrict j L
  have := coherentPresentation_restrict j N
  have hj : Function.Bijective (((restrictFunctor j).map f).app ⊤) := by
    change Function.Bijective (f.app (j ''ᵁ ⊤))
    rwa [j.image_top_eq_opensRange, hU.opensRange_fromSpec]
  have hi : IsIso ((restrictFunctor j).map f) := affine_isIso_of_sections _ hj
  apply Hom.isIso_iff_isIso_app.mpr
  intro V
  let W := U.ι ''ᵁ V
  have hWU : W ≤ U := by
    simpa only [Scheme.Opens.opensRange_ι] using U.ι.image_le_opensRange V
  have he : j ''ᵁ (j ⁻¹ᵁ W) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, hU.opensRange_fromSpec,
      inf_eq_right.mpr hWU]
  have hh := Hom.isIso_iff_isIso_app.mp hi (j ⁻¹ᵁ W)
  change IsIso (f.app (j ''ᵁ (j ⁻¹ᵁ W))) at hh
  rw [he] at hh
  exact hh

/-- Equality of section images makes the inclusion of comparable subsheaves invertible. -/
lemma inclusion_app_bijective (a : L ⟶ M) (b : N ⟶ M) [Mono a] [Mono b]
    (h : Subobject.mk a ≤ Subobject.mk b) (U : X.Opens)
    (he : LinearMap.range (a.val.app (op U)).hom =
      LinearMap.range (b.val.app (op U)).hom) :
    Function.Bijective ((Subobject.ofMkLEMk a b h).app U) := by
  let c := Subobject.ofMkLEMk a b h
  have hc (s : Γ(L, U)) : b.app U (c.app U s) = a.app U s :=
    congr($(congrArg (fun f : L ⟶ M ↦ f.app U) (Subobject.ofMkLEMk_comp h)) s)
  constructor
  · intro s t hst
    apply app_injective a U
    rw [← hc, ← hc, hst]
  · intro t
    have ht : b.app U t ∈ LinearMap.range (a.val.app (op U)).hom :=
      he ▸ LinearMap.mem_range_self (b.val.app (op U)).hom t
    obtain ⟨s, hs⟩ := ht
    exact ⟨s, app_injective b U ((hc s).trans hs)⟩

/-- Equality of affine section images on a cover identifies comparable coherent subsheaves. -/
theorem subobject_eq_of_affine_images [L.IsFinitePresentation] [N.IsFinitePresentation]
    (a : L ⟶ M) (b : N ⟶ M) [Mono a] [Mono b]
    (h : Subobject.mk a ≤ Subobject.mk b) {ι : Type u} (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)
    (he : ∀ i, LinearMap.range (a.val.app (op (U i))).hom =
      LinearMap.range (b.val.app (op (U i))).hom) : Subobject.mk a = Subobject.mk b := by
  let c := Subobject.ofMkLEMk a b h
  have hi : IsIso c := ModuleSheafOpenIsoDetection.isIso_of_iSup_eq_top c U hcover
    (fun i ↦ isIso_restrict_of_affine_sections c (hU i)
      (inclusion_app_bijective a b h (U i) (he i)))
  exact Subobject.mk_eq_mk_of_comm a b (asIso c) (Subobject.ofMkLEMk_comp h)

/-- Images of comparable subsheaves are comparable on every open. -/
lemma section_image_mono (a : L ⟶ M) (b : N ⟶ M) [Mono a] [Mono b]
    (h : Subobject.mk a ≤ Subobject.mk b) (U : X.Opens) :
    LinearMap.range (a.val.app (op U)).hom ≤ LinearMap.range (b.val.app (op U)).hom := by
  rintro _ ⟨s, rfl⟩
  refine ⟨(Subobject.ofMkLEMk a b h).app U s, ?_⟩
  exact congr($(congrArg (fun f : L ⟶ M ↦ f.app U) (Subobject.ofMkLEMk_comp h)) s)

/-- Any ascending sequence of actual coherent subsheaves of a coherent sheaf stabilizes. -/
theorem ascending_chain_stabilizes [IsNoetherian X] [M.IsFinitePresentation]
    (N : ℕ → X.Modules) [∀ n, (N n).IsFinitePresentation]
    (a : ∀ n, N n ⟶ M) [∀ n, Mono (a n)]
    (ha : Monotone (fun n ↦ Subobject.mk (a n))) :
    ∃ n, ∀ m, n ≤ m → Subobject.mk (a n) = Subobject.mk (a m) := by
  classical
  let C := X.affineCover.finiteSubcover
  let U : C.I₀ → X.Opens := fun i ↦ (C.f i).opensRange
  have hU (i : C.I₀) : IsAffineOpen (U i) := by
    have : IsAffine (C.X i) := by
      change IsAffine (X.affineCover.finiteSubcover.X i)
      rw [X.affineCover.finiteSubcover_X]
      infer_instance
    exact isAffineOpen_opensRange (C.f i)
  have hs (i : C.I₀) : ∃ n, ∀ m, n ≤ m →
      LinearMap.range ((a n).val.app (op (U i))).hom =
        LinearMap.range ((a m).val.app (op (U i))).hom := by
    have : IsNoetherianRing Γ(X, U i) :=
      IsLocallyNoetherian.component_noetherian ⟨U i, hU i⟩
    have := coherentAffineOpen_sections_finite M (hU i)
    have hn : _root_.IsNoetherian Γ(X, U i) (M.val.obj (op (U i))) :=
      isNoetherian_of_isNoetherianRing_of_finite _ _
    exact monotone_stabilizes_iff_noetherian.mpr hn
      ⟨fun n ↦ LinearMap.range ((a n).val.app (op (U i))).hom,
        fun n m h ↦ section_image_mono (a n) (a m) (ha h) (U i)⟩
  choose k hk using hs
  let n := Finset.univ.sup k
  refine ⟨n, fun m hm ↦ subobject_eq_of_affine_images (a n) (a m) (ha hm)
    U hU C.iSup_opensRange ?_⟩
  intro i
  have hi : k i ≤ n := Finset.le_sup (f := k) (Finset.mem_univ i)
  exact (hk i n hi).symm.trans (hk i m (hi.trans hm))

/-- Intrinsic formulation for chains in the poset of subobjects with coherent domains. -/
theorem coherent_subobject_chain_stabilizes [IsNoetherian X] [M.IsFinitePresentation]
    (P : ℕ →o Subobject M) (hP : ∀ n, (P n : X.Modules).IsFinitePresentation) :
    ∃ n, ∀ m, n ≤ m → P n = P m := by
  have (n : ℕ) : (P n : X.Modules).IsFinitePresentation := hP n
  simpa only [Subobject.mk_arrow] using ascending_chain_stabilizes
    (fun n ↦ (P n : X.Modules)) (fun n ↦ (P n).arrow)
    (by simpa only [Subobject.mk_arrow] using P.monotone)

end FLT.Mazur.CoherentSubsheafACC
