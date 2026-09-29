/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealModuleSheaf
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Descent of a module sheaf from a unit cocycle

Sections are tuples of functions on the chart intersections. Compatibility is
expressed on every subopen of an overlap, making restriction strictly functorial.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve
namespace ModuleSheafUnitCocycle

variable {X : Scheme.{u}}

/-- Restriction of a regular function along an inclusion of opens. -/
abbrev res {V W : X.Opens} (h : W ≤ V) : Γ(X, V) →+* Γ(X, W) :=
  (X.presheaf.map (homOfLE h).op).hom

@[simp] lemma res_res {V W Z : X.Opens} (h : W ≤ V) (k : Z ≤ W) (s : Γ(X, V)) :
    res k (res h s) = res (k.trans h) s := by
  exact (congr($(X.presheaf.map_comp (homOfLE h).op (homOfLE k).op) s)).symm

@[simp] lemma res_self {V : X.Opens} (h : V ≤ V) (s : Γ(X, V)) : res h s = s := by
  change X.presheaf.map (𝟙 (op V)) s = s
  simp

/-- A unit cocycle, including its restrictions to all subopens of each overlap. -/
structure Cocycle {ι : Type u} (U : ι → X.Opens) where
  /-- The transition unit from the j-th chart to the i-th on a common subopen. -/
  unit (i j : ι) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j) : Γ(X, V)ˣ
  natural (i j : ι) {V W : X.Opens} (h : W ≤ V) (hi : V ≤ U i) (hj : V ≤ U j) :
    res h (unit i j V hi hj : Γ(X, V)) = unit i j W (h.trans hi) (h.trans hj)
  refl (i : ι) (V : X.Opens) (h : V ≤ U i) : unit i i V h h = 1
  cocycle (i j k : ι) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j)
      (hk : V ≤ U k) : unit i j V hi hj * unit j k V hj hk = unit i k V hi hk

variable {ι : Type u} {U : ι → X.Opens} (g : Cocycle U)

namespace Cocycle

/-- Construct the natural family from units on pairwise overlaps and their cocycle law. -/
def ofOverlap (t : ∀ i j, Γ(X, U i ⊓ U j)ˣ)
    (ht : ∀ i, t i i = 1)
    (hc : ∀ i j k (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k),
      res (le_inf hi hj) (t i j : Γ(X, U i ⊓ U j)) *
        res (le_inf hj hk) (t j k : Γ(X, U j ⊓ U k)) =
          res (le_inf hi hk) (t i k : Γ(X, U i ⊓ U k))) : Cocycle U where
  unit i j V hi hj := Units.map (res (le_inf hi hj)).toMonoidHom (t i j)
  natural i j V W h hi hj := res_res _ _ _
  refl i V h := by simp [ht]
  cocycle i j k V hi hj hk := by
    apply Units.ext
    exact hc i j k V hi hj hk

/-- The componentwise scalar action is restriction followed by multiplication. -/
instance componentModule (V : X.Opens) (i : ι) : Module Γ(X, V) Γ(X, V ⊓ U i) :=
  Module.compHom Γ(X, V ⊓ U i) (res (show V ⊓ U i ≤ V from inf_le_left))

/-- Compatible tuples form a submodule of the product of chart sections. -/
def sections (V : X.Opens) : Submodule Γ(X, V) (∀ i, Γ(X, V ⊓ U i)) where
  carrier := {s | ∀ i j W (hi : W ≤ V ⊓ U i) (hj : W ≤ V ⊓ U j),
    res hi (s i) = (g.unit i j W (hi.trans inf_le_right) (hj.trans inf_le_right) :
      Γ(X, W)) * res hj (s j)}
  zero_mem' := by simp
  add_mem' := by
    intro s t hs ht i j W hi hj
    simp only [Pi.add_apply, map_add, hs i j W hi hj, ht i j W hi hj, mul_add]
  smul_mem' := by
    intro r s hs i j W hi hj
    change res hi (res inf_le_left r * s i) = _ * res hj (res inf_le_left r * s j)
    simp only [map_mul, res_res, hs i j W hi hj]
    ring

/-- Componentwise restriction preserves the transition equations. -/
def restrict {V W : X.Opens} (h : W ≤ V) (s : g.sections V) : g.sections W :=
  ⟨fun i ↦ res (inf_le_inf_right (U i) h) (s.1 i), by
    intro i j Z hi hj
    simp only [res_res]
    exact s.2 i j Z (hi.trans (inf_le_inf_right _ h))
      (hj.trans (inf_le_inf_right _ h))⟩

@[simp] lemma restrict_apply {V W : X.Opens} (h : W ≤ V) (s : g.sections V) (i : ι) :
    (g.restrict h s).1 i = res (inf_le_inf_right (U i) h) (s.1 i) := rfl

/-- The additive presheaf of compatible tuples. -/
def addPresheaf : TopCat.Presheaf Ab X where
  obj V := AddCommGrpCat.of (g.sections V.unop)
  map f := AddCommGrpCat.ofHom
    { toFun := g.restrict (leOfHom f.unop)
      map_zero' := by ext i; exact map_zero _
      map_add' := by intros; ext i; exact map_add _ _ _ }
  map_id V := by ext s i; exact res_self _ _
  map_comp f k := by ext s i; exact (res_res _ _ _).symm

instance moduleSheafUnitCocycleInst1 (V : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj V) ((g.addPresheaf).obj V) := inferInstanceAs
  (Module Γ(X, V.unop) (g.sections V.unop))

/-- The module presheaf of compatible tuples. -/
def presheaf : X.PresheafOfModules :=
  PresheafOfModules.ofPresheaf g.addPresheaf (fun V W f r s ↦ by
    apply Subtype.ext
    funext i
    change res _ (res inf_le_left r * s.1 i) =
      res inf_le_left (res (leOfHom f.unop) r) * res _ (s.1 i)
    simp only [map_mul, res_res])

/-- Compatible local tuples glue componentwise in the structure sheaf. -/
lemma isSheaf : TopCat.Presheaf.IsSheaf g.addPresheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro κ V sf hf
  have hc (i : ι) : (⨆ a, V a) ⊓ U i ≤ ⨆ a, V a ⊓ U i := by
    rw [iSup_inf_eq]
  have ht (i : ι) := X.sheaf.existsUnique_gluing' (fun a ↦ V a ⊓ U i)
    ((⨆ a, V a) ⊓ U i) (fun a ↦ homOfLE (inf_le_inf_right _ (le_iSup V a)))
    (hc i) (fun a ↦ (sf a).1 i) (by
      intro a b
      have h := congrArg (fun s : g.sections (V a ⊓ V b) ↦ s.1 i) (hf a b)
      change res _ ((sf a).1 i) = res _ ((sf b).1 i) at h
      have k : (V a ⊓ U i) ⊓ (V b ⊓ U i) ≤ (V a ⊓ V b) ⊓ U i := by
        exact le_inf (le_inf (inf_le_left.trans inf_le_left)
          (inf_le_right.trans inf_le_left)) (inf_le_left.trans inf_le_right)
      have hh := congrArg (res k) h
      change res inf_le_left ((sf a).1 i) = res inf_le_right ((sf b).1 i)
      simpa only [res_res] using hh)
  choose t ht hu using ht
  have ht' (a : κ) (i : ι) :
      res (inf_le_inf_right (U i) (le_iSup V a)) (t i) = (sf a).1 i := ht i a
  let s : g.sections (⨆ a, V a) := ⟨t, by
    intro i j W hi hj
    apply X.sheaf.eq_of_locally_eq' (fun a ↦ W ⊓ V a) W
      (fun _ ↦ homOfLE inf_le_left) (by
        rw [← inf_iSup_eq]
        exact le_inf le_rfl (hi.trans inf_le_left))
    intro a
    change res inf_le_left (res hi (t i)) =
      res inf_le_left (_ * res hj (t j))
    rw [map_mul, g.natural]
    have ei := congrArg
      (res (show W ⊓ V a ≤ V a ⊓ U i from
        le_inf inf_le_right (inf_le_left.trans (hi.trans inf_le_right)))) (ht' a i)
    have ej := congrArg
      (res (show W ⊓ V a ≤ V a ⊓ U j from
        le_inf inf_le_right (inf_le_left.trans (hj.trans inf_le_right)))) (ht' a j)
    simp only [res_res] at ei ej ⊢
    rw [ei, ej]
    exact (sf a).2 i j (W ⊓ V a) _ _⟩
  refine ⟨s, ?_, ?_⟩
  · intro a
    apply Subtype.ext
    funext i
    exact ht' a i
  · intro s' hs'
    apply Subtype.ext
    funext i
    apply hu i
    intro a
    exact congrArg (fun s : g.sections (V a) ↦ s.1 i) (hs' a)

/-- The descended module sheaf, constructed solely from the unit cocycle. -/
def sheaf : X.Modules := ⟨g.presheaf, g.isSheaf⟩

end Cocycle
end ModuleSheafUnitCocycle
end FLT.Mazur.FCurve
