/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NormalizedSectionLineBaseChange
public import FLT.Mazur.AffineTildePullbackSectionMap

/-!
# Actual sheaf lines from normalized section submodules

Affine tilde turns the normalized line into a split sheaf subobject of the
coordinate module. Its proved scalar-extension property yields an actual
pullback isomorphism, normalized on original sections by coefficient extension.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.NormalizedSectionLine
variable {R S : Type u} [CommRing R] [CommRing S] {ι : Type u}

/-- A normalized section submodule defines an actual quasi-coherent sheaf. -/
abbrev sheaf (i : ι) (L : Chart R ι i) : (Spec (.of R)).Modules :=
  tilde (ModuleCat.of R L.val)

/-- The actual inclusion into the sheaf of coordinate vectors. -/
def sheafInclusion (i : ι) (L : Chart R ι i) :
    sheaf i L ⟶ tilde (ModuleCat.of R (ι → R)) :=
  (tilde.functor (.of R)).map (ModuleCat.ofHom L.val.subtype)

/-- The module retraction of the inclusion, constructed from the coordinate trivialization. -/
def retraction (i : ι) (L : Chart R ι i) : (ι → R) →ₗ[R] L.val :=
  (trivialization R ι i L).symm.toLinearMap.comp (LinearMap.proj i)

/-- The constructed retraction is a left inverse to the actual inclusion. -/
lemma retraction_subtype (i : ι) (L : Chart R ι i) :
    (retraction i L).comp L.val.subtype = LinearMap.id := by
  apply LinearMap.ext
  intro v
  exact (trivialization R ι i L).symm_apply_apply v

/-- The actual sheaf inclusion is split by the coordinate retraction. -/
def sheafInclusionSplit (i : ι) (L : Chart R ι i) : SplitMono (sheafInclusion i L) where
  retraction := (tilde.functor (.of R)).map (ModuleCat.ofHom (retraction i L))
  id := by
    rw [sheafInclusion, ← Functor.map_comp]
    have h : ModuleCat.ofHom L.val.subtype ≫ ModuleCat.ofHom (retraction i L) =
        𝟙 (ModuleCat.of R L.val) := ModuleCat.hom_ext (retraction_subtype i L)
    rw [h]
    exact (tilde.functor (.of R)).map_id _

instance (i : ι) (L : Chart R ι i) : IsSplitMono (sheafInclusion i L) :=
  IsSplitMono.mk' (sheafInclusionSplit i L)

/-- The sheaf is genuinely trivial of rank one via its coordinate projection. -/
def sheafTrivialization (i : ι) (L : Chart R ι i) :
    sheaf i L ≅ tilde (ModuleCat.of R R) :=
  (tilde.functor (.of R)).mapIso (trivialization R ι i L).toModuleIso

/-- Pullback of the actual sheaf line is the sheaf of its extended section submodule. -/
def sheafBaseChange (φ : R →+* S) (i : ι) (L : Chart R ι i) :
    (pullback (Spec.map (CommRingCat.ofHom φ))).obj (sheaf i L) ≅
      sheaf i (baseChange φ i L) :=
  AffineTildeBaseChangeIso.iso (CommRingCat.ofHom φ) (ModuleCat.of R L.val)
    (ModuleCat.of S (baseChange φ i L).val) (coefficientMap φ i L)
    (coefficientMap_isBaseChange φ i L)

/-- The comparison is the sheaf map induced by the original coefficient map. -/
lemma sheafBaseChange_hom (φ : R →+* S) (i : ι) (L : Chart R ι i) :
    (sheafBaseChange φ i L).hom =
      AffineTildeSemilinearMap.map (CommRingCat.ofHom φ) (ModuleCat.of R L.val)
        (ModuleCat.of S (baseChange φ i L).val) (coefficientMap φ i L) :=
  AffineTildeBaseChangeIso.iso_hom _ _ _ _ _

attribute [local irreducible] sheafBaseChange AffineTildeSemilinearMap.map
attribute [local irreducible] AffineTildePullbackSectionMap.unit moduleSpecΓFunctor

/-- Original sections pull back by applying the ring map to every coordinate. -/
lemma sheafBaseChange_unit (φ : R →+* S) (i : ι) (L : Chart R ι i) (v : L.val) :
    moduleSpecΓFunctor.map (sheafBaseChange φ i L).hom
        (AffineTildePullbackSectionMap.unit (CommRingCat.ofHom φ) (ModuleCat.of R L.val) v) =
      (tilde.toTildeΓNatIso (R := .of S)).hom.app
        (ModuleCat.of S (baseChange φ i L).val) (coefficientMap φ i L v) := by
  rw [sheafBaseChange_hom]
  exact AffineTildePullbackSectionMap.semilinearMap_unit (CommRingCat.ofHom φ)
    (ModuleCat.of R L.val) (ModuleCat.of S (baseChange φ i L).val) (coefficientMap φ i L) v

end FLT.Mazur.NormalizedSectionLine
