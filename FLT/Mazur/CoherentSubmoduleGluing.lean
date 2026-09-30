/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentSubmoduleEnlargement
public import FLT.Mazur.ModuleSheafGluing
public import FLT.Mazur.CoherentOpenDescent

/-!
# Gluing coherent submodules

Equal overlap subobjects determine the transition maps, their cocycle, and a
coherent submodule of the ambient module.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules FLT.Mazur.ModuleSheafMorphismGluing

universe u

namespace FLT.Mazur.CoherentSubmoduleGluing

variable {X : Scheme.{u}}

/-- The restriction unit is invertible on any slice inside its open chart. -/
lemma unit_over_isIso (M : X.Modules) {U V : X.Opens} (h : V ≤ U) :
    IsIso (((restrictAdjunction U.ι).unit.app M).over V) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.forget _),
    ← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
  rw [NatTrans.isIso_iff_isIso_app]
  intro W
  change IsIso (M.presheaf.map
    (homOfLE (U.ι.image_preimage_le W.unop.left)).op)
  have he : U.ι ''ᵁ (U.ι ⁻¹ᵁ W.unop.left) = W.unop.left := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr ((leOfHom W.unop.hom).trans h)]
  have hh : (homOfLE (U.ι.image_preimage_le W.unop.left)).op = (eqToHom he).op :=
    Subsingleton.elim _ _
  rw [hh]
  infer_instance

/-- A chart inclusion, transported to any smaller ambient slice. -/
def inclusionOn (M : X.Modules) {U : X.Opens} {L : U.toScheme.Modules}
    (a : L ⟶ M.restrict U.ι) {V : X.Opens} (h : V ≤ U) :
    ((pushforward U.ι).obj L).over V ⟶ M.over V :=
  letI := unit_over_isIso M h
  ((pushforward U.ι).map a).over V ≫ inv (((restrictAdjunction U.ι).unit.app M).over V)

/-- Transported inclusions remain monomorphisms. -/
instance inclusionOn_mono (M : X.Modules) {U : X.Opens} {L : U.toScheme.Modules}
    (a : L ⟶ M.restrict U.ι) [Mono a] {V : X.Opens} (h : V ≤ U) :
    Mono (inclusionOn M a h) := by
  let := unit_over_isIso M h
  have hp : Mono (((pushforward U.ι).map a).over V) := by
    apply (SheafOfModules.forget _).mono_of_mono_map
    apply PresheafOfModules.mono_of_injective
    intro W
    exact ModuleSubobjectCoverEquality.app_injective ((pushforward U.ι).map a) W.unop.left
  exact mono_comp _ _

/-- A monomorphism on a slice is injective on every subopen. -/
lemma localApp_injective {P Q : X.Modules} {U V : X.Opens}
    (a : P.over U ⟶ Q.over U) [Mono a] (h : V ≤ U) :
    Function.Injective (localApp a h) := by
  have : Mono a.val := (SheafOfModules.forget _).map_mono a
  exact PresheafOfModules.injective_of_mono a.val (op (Over.mk (homOfLE h)))

/-- The transported inclusion commutes with the restriction unit. -/
lemma inclusionOn_unit (M : X.Modules) {U : X.Opens} {L : U.toScheme.Modules}
    (a : L ⟶ M.restrict U.ι) {V : X.Opens} (h : V ≤ U) :
    inclusionOn M a h ≫ ((restrictAdjunction U.ι).unit.app M).over V =
      ((pushforward U.ι).map a).over V := by
  let := unit_over_isIso M h
  simp [inclusionOn]

/-- The inclusion evaluated on a subopen is independent of its containing slice. -/
lemma inclusionOn_localApp (M : X.Modules) {U V W S : X.Opens}
    {L : U.toScheme.Modules} (a : L ⟶ M.restrict U.ι)
    (hV : V ≤ U) (hW : W ≤ U) (hS : S ≤ V) (hS' : S ≤ W) :
    localApp (inclusionOn M a hV) hS = localApp (inclusionOn M a hW) hS' := by
  let := unit_over_isIso M (hS.trans hV)
  have hj := localApp_injective (((restrictAdjunction U.ι).unit.app M).over S) le_rfl
  ext s
  apply hj
  exact (congrArg (fun f ↦ localApp f hS s) (inclusionOn_unit M a hV)).trans
    (congrArg (fun f ↦ localApp f hS' s) (inclusionOn_unit M a hW)).symm

/-- The restriction equivalence respects composition. -/
lemma restrictionEquiv_comp {P Q R : X.Modules} (U : X.Opens)
    (a : P.over U ⟶ Q.over U) (b : Q.over U ⟶ R.over U) :
    restrictionEquiv U (a ≫ b) = restrictionEquiv U a ≫ restrictionEquiv U b := by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  rfl

/-- The restriction equivalence preserves monomorphisms. -/
instance restrictionEquiv_mono {P Q : X.Modules} (U : X.Opens)
    (a : P.over U ⟶ Q.over U) [Mono a] : Mono (restrictionEquiv U a) := by
  apply (SheafOfModules.forget _).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro W
  exact localApp_injective a (U.ι_image_le W.unop)

/-- Lift an isomorphism of geometric restrictions to the ambient slice. -/
def liftIso {P Q : X.Modules} (U : X.Opens)
    (e : P.restrict U.ι ≅ Q.restrict U.ι) : P.over U ≅ Q.over U where
  hom := (restrictionEquiv U).symm e.hom
  inv := (restrictionEquiv U).symm e.inv
  hom_inv_id := by
    apply (restrictionEquiv U).injective
    rw [restrictionEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      e.hom_inv_id]
    rfl
  inv_hom_id := by
    apply (restrictionEquiv U).injective
    rw [restrictionEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      e.inv_hom_id]
    rfl

/-- The transported slice inclusion recovers the original chart inclusion via the counit. -/
lemma inclusionOn_restriction (M : X.Modules) {U : X.Opens} {L : U.toScheme.Modules}
    (a : L ⟶ M.restrict U.ι) :
    restrictionEquiv U (inclusionOn M a le_rfl) =
      (restrictFunctorAdjCounitIso U.ι).hom.app L ≫ a := by
  have hi := congrArg (restrictionEquiv U) (inclusionOn_unit M a le_rfl)
  rw [restrictionEquiv_comp, restrictionEquiv_over, restrictionEquiv_over] at hi
  let F := restrictFunctor U.ι
  let adj := restrictAdjunction U.ι
  change restrictionEquiv U (inclusionOn M a le_rfl) = adj.counit.app L ≫ a
  calc
    _ = restrictionEquiv U (inclusionOn M a le_rfl) ≫
        F.map (adj.unit.app M) ≫ adj.counit.app (M.restrict U.ι) := by
      rw [adj.left_triangle_components, Category.comp_id]
    _ = F.map ((pushforward U.ι).map a) ≫ adj.counit.app (M.restrict U.ι) := by
      rw [← Category.assoc, hi]
    _ = adj.counit.app L ≫ a := adj.counit.naturality a

variable {ι : Type u} (U : ι → X.Opens) (M : X.Modules)
    (L : ∀ i, (U i).toScheme.Modules) (a : ∀ i, L i ⟶ M.restrict (U i).ι)
    [∀ i, Mono (a i)]

/-- Compatibility is equality of the actual restricted overlap subobjects. -/
def CompatibleInclusions : Prop := ∀ i j,
  Subobject.mk (restrictionEquiv (U i ⊓ U j) (inclusionOn M (a i) inf_le_left)) =
    Subobject.mk (restrictionEquiv (U i ⊓ U j) (inclusionOn M (a j) inf_le_right))

variable {U M L a} (ha : CompatibleInclusions U M L a)

/-- Equality of overlap subobjects constructs the transition without a choice of gluing data. -/
def transition (i j : ι) :
    ((pushforward (U i).ι).obj (L i)).over (U i ⊓ U j) ≅
      ((pushforward (U j).ι).obj (L j)).over (U i ⊓ U j) :=
  liftIso (U i ⊓ U j) (Subobject.isoOfMkEqMk _ _ (ha i j))

/-- The canonical transition identifies the overlap inclusions. -/
lemma transition_inclusion (i j : ι) :
    (transition ha i j).hom ≫ inclusionOn M (a j) inf_le_right =
      inclusionOn M (a i) inf_le_left := by
  apply (restrictionEquiv (U i ⊓ U j)).injective
  rw [restrictionEquiv_comp]
  simp only [transition, liftIso, Equiv.apply_symm_apply,
    Subobject.isoOfMkEqMk_hom, Subobject.ofMkLEMk_comp]

/-- On each subopen, the transition preserves the actual ambient section. -/
lemma transition_local (i j : ι) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j) (s) :
    localApp (inclusionOn M (a j) le_rfl) hj
      (localApp (transition ha i j).hom (le_inf hi hj) s) =
    localApp (inclusionOn M (a i) le_rfl) hi s := by
  rw [inclusionOn_localApp M (a j) le_rfl inf_le_right hj (le_inf hi hj),
    inclusionOn_localApp M (a i) le_rfl inf_le_left hi (le_inf hi hj)]
  exact congrArg (fun f ↦ localApp f (le_inf hi hj) s) (transition_inclusion ha i j)

/-- Cancellation of a common inclusion proves the transition cocycle. -/
lemma transition_cocycle (i j k : ι) (V : X.Opens) (hi : V ≤ U i)
    (hj : V ≤ U j) (hk : V ≤ U k) (s) :
    localApp (transition ha j k).hom (le_inf hj hk)
      (localApp (transition ha i j).hom (le_inf hi hj) s) =
        localApp (transition ha i k).hom (le_inf hi hk) s := by
  apply localApp_injective (inclusionOn M (a k) le_rfl) hk
  rw [transition_local ha j k V hj hk, transition_local ha i j V hi hj,
    transition_local ha i k V hi hk]

/-- Gluing data is constructed solely from the inclusions and their overlap equality. -/
def data : ModuleSheafGluing.Data U where
  obj := L
  transition := transition ha
  cocycle := transition_cocycle ha

/-- Each projection followed by its chart inclusion maps locally into the ambient module. -/
def localInclusion (i : ι) : (data ha).glued.over (U i) ⟶ M.over (U i) :=
  ((data ha).projection i).over (U i) ≫ inclusionOn M (a i) le_rfl

/-- The local inclusions agree because the families obey the canonical transitions. -/
lemma localInclusion_compatible : Compatible U (localInclusion ha) := by
  intro i j V hi hj
  ext s
  have hs := s.property i j V le_rfl hi hj
  simp only [res_self] at hs
  change localApp (inclusionOn M (a i) le_rfl) hi (s.val i) =
    localApp (inclusionOn M (a j) le_rfl) hj (s.val j)
  rw [← hs]
  exact (transition_local ha i j V hi hj (s.val i)).symm

/-- The glued object maps to the original ambient module. -/
def inclusion (hU : iSup U = ⊤) : (data ha).glued ⟶ M :=
  glue U hU (localInclusion ha) (localInclusion_compatible ha)

/-- On each slice the glued inclusion is the prescribed local inclusion. -/
lemma inclusion_over (hU : iSup U = ⊤) (i : ι) :
    (inclusion ha hU).over (U i) = localInclusion ha i :=
  glue_over U hU (localInclusion ha) (localInclusion_compatible ha) i

/-- The chart isomorphisms identify the constructed inclusion with the given one. -/
lemma restriction_commutes (hU : iSup U = ⊤) (i : ι) :
    ((data ha).restrictionIso i).hom ≫ a i =
      (restrictFunctor (U i).ι).map (inclusion ha hU) := by
  rw [← restrictionEquiv_over, inclusion_over]
  change _ = restrictionEquiv (U i)
    (((data ha).projection i).over (U i) ≫ inclusionOn M (a i) le_rfl)
  rw [restrictionEquiv_comp, restrictionEquiv_over, inclusionOn_restriction]
  exact Category.assoc _ _ _

/-- A cover of chart monomorphisms makes the glued inclusion monic. -/
instance inclusion_mono (hU : iSup U = ⊤) : Mono (inclusion ha hU) where
  right_cancellation {Z} f g h := by
    apply hom_ext_restrict U hU
    intro i
    have : Mono (((data ha).restrictionIso i).hom ≫ a i) := inferInstance
    apply (cancel_mono (((data ha).restrictionIso i).hom ≫ a i)).mp
    rw [restriction_commutes, ← Functor.map_comp, ← Functor.map_comp, h]

/-- Local finite presentations of the prescribed charts descend to the constructed object. -/
theorem coherent (hU : iSup U = ⊤) [∀ i, (L i).IsFinitePresentation] :
    (data ha).glued.IsFinitePresentation := by
  apply FCurve.coherent_of_openCover (data ha).glued U hU
  intro i
  exact (SheafOfModules.isFinitePresentation (U i).toScheme.ringCatSheaf).prop_of_iso
    ((data ha).restrictionIso i).symm (inferInstanceAs (L i).IsFinitePresentation)

/-- The constructed submodule restricts to exactly the prescribed chart subobjects. -/
theorem subobject_eq (hU : iSup U = ⊤) (i : ι) :
    Subobject.mk ((restrictFunctor (U i).ι).map (inclusion ha hU)) =
      Subobject.mk (a i) := by
  have := CoherentSubmoduleEnlargement.restrictMap_mono (U i).ι (inclusion ha hU)
  exact Subobject.mk_eq_mk_of_comm _ _ ((data ha).restrictionIso i)
    (restriction_commutes ha hU i)

include ha in
/-- Compatible coherent chart inclusions glue to a coherent submodule of the ambient module. -/
theorem exists_glued (hU : iSup U = ⊤) [∀ i, (L i).IsFinitePresentation] :
    ∃ (N : X.Modules) (_ : N.IsFinitePresentation) (b : N ⟶ M) (_ : Mono b),
      ∃ e : ∀ i, N.restrict (U i).ι ≅ L i,
        ∀ i, (e i).hom ≫ a i = (restrictFunctor (U i).ι).map b :=
  ⟨(data ha).glued, coherent ha hU, inclusion ha hU, inferInstance,
    (data ha).restrictionIso, restriction_commutes ha hU⟩

end FLT.Mazur.CoherentSubmoduleGluing
