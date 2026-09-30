/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentSubmoduleUnion

/-!
# Global coherent submodule extension

A finite affine cover lets us enlarge a coherent submodule from an open to the
whole Noetherian scheme. The construction preserves the inclusion on the entire
original open, and therefore gives compatible isomorphisms on all its stalks.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules FLT.Mazur.CoherentSubmoduleEnlargement
open FLT.Mazur.CoherentSubmoduleUnion
open FLT.Mazur.FCurve.CoherentDevissage
open FLT.Mazur.FCurve.CoherentDevissage.ClosedDescentCharts
universe u
namespace FLT.Mazur.CoherentSubmoduleExtension
variable {X : Scheme.{u}} (M : X.Modules)

/-- A submodule on the top open transports to a submodule on the scheme. -/
theorem extension_top (L : (⊤ : X.Opens).toScheme.Modules)
    [L.IsFinitePresentation] (a : L ⟶ M.restrict (⊤ : X.Opens).ι) [Mono a] :
    Nonempty (Extension M ⊤ L a) := by
  let f := (⊤ : X.Opens).ι
  have : IsIso f := inferInstanceAs (IsIso X.topIso.hom)
  have hu := iso_unit_isIso f M
  let N := (pushforward f).obj L
  let b : N ⟶ M := (pushforward f).map a ≫ inv ((restrictAdjunction f).unit.app M)
  have hb : Mono b := by dsimp [b]; infer_instance
  have hN : N.IsFinitePresentation := coherentPresentation_pushforwardIso (asIso f) L
  let e := (restrictFunctorAdjCounitIso f).app L
  refine ⟨⟨N, b, hb, hN, e, ?_⟩⟩
  have ht : (restrictFunctor f).map (inv ((restrictAdjunction f).unit.app M)) =
      (restrictAdjunction f).counit.app (M.restrict f) := by
    apply (cancel_epi ((restrictFunctor f).map ((restrictAdjunction f).unit.app M))).mp
    rw [← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id]
    exact ((restrictAdjunction f).left_triangle_components M).symm
  dsimp only [b]
  rw [Functor.map_comp, ht]
  exact ((restrictAdjunction f).counit.naturality a).symm

/-- Compose the global extension on a larger open with its original comparison. -/
def descend {U V : X.Opens} (L : U.toScheme.Modules)
    (a : L ⟶ M.restrict U.ι) (E : UnionExtension M U V L a)
    (G : Extension M (U ⊔ V) E.obj E.inclusion) : Extension M U L a := by
  let h : U ≤ U ⊔ V := le_sup_left
  let F := restrictFunctor (X.homOfLE h)
  let e := ((nestedRestriction h).app G.obj).symm ≪≫
    F.mapIso G.comparison ≪≫ E.comparison
  refine ⟨G.obj, G.inclusion, G.inclusion_mono, G.coherent, e, ?_⟩
  dsimp only [e]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_inv, Category.assoc]
  rw [E.commutes, ← Category.assoc (F.map G.comparison.hom), ← Functor.map_comp,
    G.commutes]
  have hn := (nestedRestriction h).hom.naturality G.inclusion
  simp only [Functor.comp_map] at hn
  rw [hn]
  simp

/-- Enlarge successively over a finite collection of affine opens covering the complement. -/
theorem extension_of_finset [IsLocallyNoetherian X] [M.IsFinitePresentation]
    (s : Finset X.Opens) (hs : ∀ V ∈ s, IsAffineOpen V)
    (U : X.Opens) (hcover : U ⊔ s.sup id = ⊤)
    (L : U.toScheme.Modules) [L.IsFinitePresentation]
    (a : L ⟶ M.restrict U.ι) [Mono a] : Nonempty (Extension M U L a) := by
  classical
  induction s using Finset.induction_on generalizing U with
  | empty =>
    simp only [Finset.sup_empty, sup_bot_eq] at hcover
    subst U
    exact extension_top M L a
  | @insert V s hVs ih =>
    obtain ⟨E⟩ := exists_union_extension M U V (hs V (Finset.mem_insert_self _ _)) L a
    have hc : (U ⊔ V) ⊔ s.sup id = ⊤ := by
      simpa only [Finset.sup_insert, id_eq, sup_assoc] using hcover
    obtain ⟨G⟩ := ih (fun W hW ↦ hs W (Finset.mem_insert_of_mem hW))
      (U ⊔ V) hc E.obj E.inclusion
    exact ⟨descend M L a E G⟩

/-- Every coherent submodule on an open of a Noetherian scheme extends globally.
All opens here are quasi-compact; no choice of a principal open is needed. -/
theorem exists_extension [IsNoetherian X] [M.IsFinitePresentation]
    (U : X.Opens) (L : U.toScheme.Modules) [L.IsFinitePresentation]
    (a : L ⟶ M.restrict U.ι) [Mono a] : Nonempty (Extension M U L a) := by
  classical
  let C := X.affineCover.finiteSubcover
  let V : C.I₀ → X.Opens := fun i ↦ (C.f i).opensRange
  have hV (i : C.I₀) : IsAffineOpen (V i) := by
    have : IsAffine (C.X i) := by
      change IsAffine (X.affineCover.finiteSubcover.X i)
      rw [X.affineCover.finiteSubcover_X]
      infer_instance
    exact isAffineOpen_opensRange (C.f i)
  apply extension_of_finset M (Finset.univ.image V) ?_ U ?_ L a
  · intro W hW
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hW
    exact hV i
  · have hc : (Finset.univ.image V).sup id = ⊤ := by
      simpa only [Finset.sup_image, Function.comp_def, id_eq, Finset.sup_univ_eq_iSup]
        using C.iSup_opensRange
    rw [hc, sup_top_eq]

/-- A chosen global coherent extension of the given submodule. -/
def extension [IsNoetherian X] [M.IsFinitePresentation]
    (U : X.Opens) (L : U.toScheme.Modules) [L.IsFinitePresentation]
    (a : L ⟶ M.restrict U.ι) [Mono a] : Extension M U L a :=
  (exists_extension M U L a).some

/-- The constructed global subobject restricts to the prescribed subobject. -/
theorem extension_subobject_eq [IsNoetherian X] [M.IsFinitePresentation]
    (U : X.Opens) (L : U.toScheme.Modules) [L.IsFinitePresentation]
    (a : L ⟶ M.restrict U.ι) [Mono a] :
    Subobject.mk ((restrictFunctor U.ι).map (extension M U L a).inclusion) =
      Subobject.mk a :=
  (extension M U L a).subobject_eq

/-- At each point of the original open the global extension has the prescribed stalk. -/
def stalkIso {U : X.Opens} {L : U.toScheme.Modules} {a : L ⟶ M.restrict U.ι}
    (E : Extension M U L a) (x : U.toScheme) :
    E.obj.presheaf.stalk (U.ι x) ≅ L.presheaf.stalk x :=
  ((restrictStalkNatIso U.ι x).app E.obj).symm ≪≫ (stalk x).mapIso E.comparison

/-- The stalk isomorphism intertwines the original and extended inclusions. -/
theorem stalkIso_commutes {U : X.Opens} {L : U.toScheme.Modules}
    {a : L ⟶ M.restrict U.ι} (E : Extension M U L a) (x : U.toScheme) :
    (stalkIso M E x).hom ≫ (stalk x).map a ≫
        (restrictStalkNatIso U.ι x).hom.app M = (stalk (U.ι x)).map E.inclusion := by
  simp only [stalkIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_inv,
    Category.assoc]
  rw [← Functor.map_comp_assoc, E.commutes]
  have hn := (restrictStalkNatIso U.ι x).hom.naturality E.inclusion
  change (stalk x).map ((restrictFunctor U.ι).map E.inclusion) ≫ _ =
    (restrictStalkNatIso U.ι x).hom.app E.obj ≫
      (stalk (U.ι x)).map E.inclusion at hn
  rw [hn]
  simp

end FLT.Mazur.CoherentSubmoduleExtension
