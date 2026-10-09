/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafEmptySlice
public import FLT.Mazur.ModuleSheafGluingMapRestriction

/-!
# Independent module sheaves on disjoint opens

Disjointness constructs all transitions and their cocycle. Thus arbitrary
modules and arbitrary component maps assemble without compatibility inputs.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.ModuleSheafDisjointGluing
open ModuleSheafGluing ModuleSheafMorphismGluing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
variable (hd : Pairwise (fun i j ↦ Disjoint (U i) (U j)))
variable (M : ∀ i, (U i).toScheme.Modules)

/-- Independent charts have the identity transition or the unique empty transition. -/
def transition (i j : ι) :
    ((pushforward (U i).ι).obj (M i)).over (U i ⊓ U j) ≅
      ((pushforward (U j).ι).obj (M j)).over (U i ⊓ U j) := by
  classical
  exact if h : i = j then by subst j; exact Iso.refl _
    else ModuleSheafEmptySlice.iso _ _ _ (hd h).eq_bot

@[simp]
lemma transition_self (i : ι) : transition U hd M i i = Iso.refl _ := by
  classical
  simp [transition]

include hd in
/-- A subopen of distinct components is empty. -/
lemma subopen_eq_bot {i j : ι} (h : i ≠ j) (V : X.Opens)
    (hi : V ≤ U i) (hj : V ≤ U j) : V = ⊥ :=
  le_bot_iff.mp ((le_inf hi hj).trans_eq (hd h).eq_bot)

/-- The gluing input for arbitrary modules on pairwise disjoint opens. -/
def data : Data U where
  obj := M
  transition := transition U hd M
  cocycle i j k V hi hj hk s := by
    by_cases hij : i = j
    · subst j
      simp only [transition_self]
      rfl
    · exact @Subsingleton.elim Γ((pushforward (U k).ι).obj (M k), V)
        (ModuleSheafEmptySlice.sections_subsingleton _ _
          (subopen_eq_bot U hd hij V hi hj)) _ _

/-- The module sheaf assembled from the independent chart modules. -/
def glued : X.Modules := (data U hd M).glued

/-- The assembly restricts to the independently supplied module on each chart. -/
def recovery (i : ι) : (glued U hd M).restrict (U i).ι ≅ M i :=
  (data U hd M).restrictionIso i

variable {M} {N : ∀ i, (U i).toScheme.Modules}

/-- Any family of component maps is compatible with the constructed transitions. -/
def mapData (f : ∀ i, M i ⟶ N i) : (data U hd M).Map (data U hd N) where
  app := f
  compatible i j V hi hj s := by
    by_cases hij : i = j
    · subst j
      dsimp only [Data.trans, data]
      simp only [transition_self]
      rfl
    · exact @Subsingleton.elim Γ((pushforward (U j).ι).obj (N j), V)
        (ModuleSheafEmptySlice.sections_subsingleton _ _
          (subopen_eq_bot U hd hij V hi hj)) _ _

/-- Assemble independent component maps into a map of the glued sheaves. -/
def map (hU : iSup U = ⊤) (f : ∀ i, M i ⟶ N i) : glued U hd M ⟶ glued U hd N :=
  (mapData U hd f).gluedMap hU

/-- Restriction recovers each original component map. -/
@[reassoc]
lemma map_recovery (hU : iSup U = ⊤) (f : ∀ i, M i ⟶ N i) (i : ι) :
    (restrictFunctor (U i).ι).map (map U hd hU f) ≫ (recovery U hd N i).hom =
      (recovery U hd M i).hom ≫ f i :=
  (mapData U hd f).gluedMap_restrictionIso hU i

@[simp]
lemma map_id (hU : iSup U = ⊤) :
    map U hd hU (fun i ↦ 𝟙 (M i)) = 𝟙 (glued U hd M) :=
  Data.Map.gluedMap_id hU

@[simp]
lemma map_comp {P : ∀ i, (U i).toScheme.Modules} (hU : iSup U = ⊤)
    (f : ∀ i, M i ⟶ N i) (g : ∀ i, N i ⟶ P i) :
    map U hd hU (fun i ↦ f i ≫ g i) = map U hd hU f ≫ map U hd hU g :=
  (mapData U hd f).gluedMap_comp (mapData U hd g) hU

end FLT.Mazur.ModuleSheafDisjointGluing
