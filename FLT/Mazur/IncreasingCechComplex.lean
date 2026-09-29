/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CechSheafHZero
public import Mathlib.Order.Fin.Basic

/-!
# The increasing-tuple Cech complex

Sections on strictly increasing tuples form a bounded complex for a finite
index type. Square-zero follows by restricting the full tuple differential.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace FLT.Mazur.IncreasingCechComplex

variable {X : TopCat.{u}} {ι : Type u} [LinearOrder ι]

/-- A tuple with strictly increasing entries. -/
abbrev Tuple (n : ℕ) := {a : Fin (n + 1) → ι // StrictMono a}

/-- Delete an entry of an increasing tuple. -/
def face {n : ℕ} (a : Tuple (ι := ι) (n + 1)) (k : Fin (n + 2)) : Tuple (ι := ι) n :=
  ⟨a.val ∘ k.succAbove, a.property.comp (Fin.strictMono_succAbove k)⟩

variable (U : ι → Opens X) (F : TopCat.Sheaf AddCommGrpCat.{u} X)

/-- Sections on all tuple intersections. -/
abbrev FullTerm (n : ℕ) :=
  ∀ a : Fin (n + 1) → ι, F.obj.obj (op (CechSheafHZero.V U n a))

/-- Sections on increasing tuple intersections. -/
abbrev Term (n : ℕ) :=
  ∀ a : Tuple (ι := ι) n, F.obj.obj (op (CechSheafHZero.V U n a.val))

omit [LinearOrder ι] in
/-- Deleting an entry enlarges the intersection. -/
lemma face_le (n : ℕ) (a : Fin (n + 2) → ι) (k : Fin (n + 2)) :
    CechSheafHZero.V U (n + 1) a ≤ CechSheafHZero.V U n (a ∘ k.succAbove) :=
  le_iInf fun j ↦ iInf_le _ (k.succAbove j)

/-- The coface restricts a section from the deleted tuple. -/
def coface (n : ℕ) (k : Fin (n + 2)) : Term U F n →+ Term U F (n + 1) where
  toFun x a := F.obj.map (homOfLE (face_le U n a.val k)).op (x (face a k))
  map_zero' := by ext; exact map_zero _
  map_add' x y := by ext; exact map_add _ _ _

/-- The integral alternating sum of restriction cofaces. -/
def differential (n : ℕ) : Term U F n →+ Term U F (n + 1) :=
  ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • coface U F n k

lemma differential_apply (n : ℕ) (x : Term U F n) (a : Tuple (ι := ι) (n + 1)) :
    differential U F n x a = ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
      F.obj.map (homOfLE (face_le U n a.val k)).op (x (face a k)) := by
  simp [differential, coface, AddMonoidHom.finsetSum_apply]

/-- Restrict arbitrary tuple coordinates to increasing tuples. -/
def restrict (n : ℕ) : FullTerm U F n →+ Term U F n where
  toFun x a := x a.val
  map_zero' := rfl
  map_add' _ _ := rfl

lemma restrict_surjective (n : ℕ) : Function.Surjective (restrict U F n) := by
  classical
  intro x
  refine ⟨fun a ↦ if h : StrictMono a then x ⟨a, h⟩ else 0, ?_⟩
  funext a
  exact dite_eq_left a.property

omit [LinearOrder ι] in
/-- The full coface formula in section coordinates, in every degree. -/
lemma full_coface (n : ℕ) (k : Fin (n + 2)) (x : (CechSheafHZero.C U F).X n)
    (a : Fin (n + 2) → ι) :
    CechSheafHZero.termEquiv U F (n + 1) ((CechSheafHZero.cosimplicial U F).δ k x) a =
      F.obj.map (homOfLE (face_le U n a k)).op
        (CechSheafHZero.termEquiv U F n x (a ∘ k.succAbove)) := by
  have hp : (CechSheafHZero.cosimplicial U F).δ k ≫
      Pi.π (fun b : Fin (n + 2) → ι ↦ F.obj.obj (op (∏ᶜ (U ∘ b)))) a =
      Pi.π (fun b : Fin (n + 1) → ι ↦ F.obj.obj (op (∏ᶜ (U ∘ b))))
        (a ∘ k.succAbove) ≫
          F.obj.map (Pi.lift (fun j : Fin (n + 1) ↦ Pi.π (U ∘ a) (k.succAbove j))).op := by
    change Pi.lift _ ≫ Pi.π _ a = _
    rw [Pi.lift_comp_π]
    rfl
  rw [CechSheafHZero.termEquiv_apply, CechSheafHZero.termEquiv_apply]
  simp only [← ConcreteCategory.comp_apply]
  erw [← ConcreteCategory.comp_apply]
  apply ConcreteCategory.congr_hom
  rw [← Category.assoc, hp]
  simp only [Category.assoc, ← Functor.map_comp]
  congr 2

omit [LinearOrder ι] in
/-- The full differential is the signed sum of restrictions. -/
lemma full_differential (n : ℕ) (x : (CechSheafHZero.C U F).X n)
    (a : Fin (n + 2) → ι) :
    CechSheafHZero.termEquiv U F (n + 1) ((CechSheafHZero.C U F).d n (n + 1) x) a =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        F.obj.map (homOfLE (face_le U n a k)).op
          (CechSheafHZero.termEquiv U F n x (a ∘ k.succAbove)) := by
  have hd : (CechSheafHZero.C U F).d n (n + 1) =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • (CechSheafHZero.cosimplicial U F).δ k := by
    change (AlgebraicTopology.AlternatingCofaceMapComplex.obj
      (CechSheafHZero.cosimplicial U F)).d n (n + 1) = _
    dsimp only [AlgebraicTopology.AlternatingCofaceMapComplex.obj]
    rw [CochainComplex.of_d]
    rfl
  rw [hd]
  change CechSheafHZero.termEquiv U F (n + 1)
    ((∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
      (CechSheafHZero.cosimplicial U F).δ k).hom x) a = _
  rw [show (∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
      (CechSheafHZero.cosimplicial U F).δ k).hom =
      ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ) •
        (CechSheafHZero.cosimplicial U F).δ k).hom from
          map_sum AddCommGrpCat.homAddEquiv _ _]
  simp only [AddCommGrpCat.hom_zsmul, AddMonoidHom.finsetSum_apply,
    AddMonoidHom.zsmul_apply, map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply,
    full_coface]

/-- Restriction of the full differential is the increasing differential. -/
lemma restrict_differential (n : ℕ) (x : (CechSheafHZero.C U F).X n) :
    restrict U F (n + 1)
      (CechSheafHZero.termEquiv U F (n + 1) ((CechSheafHZero.C U F).d n (n + 1) x)) =
        differential U F n (restrict U F n (CechSheafHZero.termEquiv U F n x)) := by
  funext a
  exact (full_differential U F n x a.val).trans (differential_apply U F n
    (restrict U F n (CechSheafHZero.termEquiv U F n x)) a).symm

/-- The increasing differential squares to zero. -/
lemma differential_sq (n : ℕ) (x : Term U F n) :
    differential U F (n + 1) (differential U F n x) = 0 := by
  obtain ⟨y, rfl⟩ := restrict_surjective U F n x
  obtain ⟨z, rfl⟩ := (CechSheafHZero.termEquiv U F n).surjective y
  rw [← restrict_differential, ← restrict_differential]
  have h := ConcreteCategory.congr_hom ((CechSheafHZero.C U F).d_comp_d n (n + 1) (n + 2)) z
  change (CechSheafHZero.C U F).d (n + 1) (n + 2)
    ((CechSheafHZero.C U F).d n (n + 1) z) = 0 at h
  rw [h, map_zero, map_zero]

/-- The Cech complex indexed only by strictly increasing tuples. -/
def complex : CochainComplex AddCommGrpCat.{u} ℕ :=
  CochainComplex.of (fun n ↦ AddCommGrpCat.of (Term U F n))
    (fun n ↦ AddCommGrpCat.ofHom (differential U F n)) (fun n ↦ by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      exact differential_sq U F n)

/-- There are no increasing tuples above the cardinal bound. -/
lemma tuple_isEmpty [Fintype ι] (n : ℕ) (h : Fintype.card ι ≤ n) :
    IsEmpty (Tuple (ι := ι) n) := by
  refine ⟨fun a ↦ ?_⟩
  have hc := Fintype.card_le_of_injective _ a.property.injective
  simp only [Fintype.card_fin] at hc
  omega

/-- Terms vanish from the cardinal bound onwards, also for an empty index type. -/
lemma term_subsingleton [Fintype ι] (n : ℕ) (h : Fintype.card ι ≤ n) :
    Subsingleton (Term U F n) := by
  let := tuple_isEmpty (ι := ι) n h
  infer_instance

/-- Categorical term vanishing at the cardinal bound. -/
lemma complex_isZero [Fintype ι] (n : ℕ) (h : Fintype.card ι ≤ n) :
    IsZero ((complex U F).X n) := by
  let := term_subsingleton U F n h
  exact AddCommGrpCat.isZero_of_subsingleton (AddCommGrpCat.of (Term U F n))

end FLT.Mazur.IncreasingCechComplex
