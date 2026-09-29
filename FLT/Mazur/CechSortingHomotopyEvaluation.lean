/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CechSortingRecursiveHomotopy
public import FLT.Mazur.CechSortingMaps

/-!
# Evaluation of the sorting homotopy in section coordinates

Integral tuple chains evaluate in dependent section groups by restricting to a
common open. Support controls these restrictions and the differential identity.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace Opposite
open scoped BigOperators

universe u

namespace FLT.Mazur.CechSortingHomotopyEvaluation

open CechSortingHomotopyCoordinates CechSortingRecursiveHomotopy
open IncreasingCechComplex CechSortingCoordinates CechSortingTupleChains

variable {X : TopCat.{u}} {ι : Type u}
variable (U : ι → Opens X) (F : TopCat.Sheaf AddCommGrpCat.{u} X)

/-- Vertices whose opens contain the target open. -/
def vertices (W : Opens X) : Set ι := {i | W ≤ U i}

/-- Actual vertex support gives the inclusion needed for restriction. -/
lemma supported_le (W : Opens X) (n : ℕ) (a : Fin (n + 1) → ι)
    (ha : ∀ i, a i ∈ vertices U W) : W ≤ CechSheafHZero.V U n a :=
  le_iInf ha

/-- Evaluate an integral chain by restricting each available coordinate. -/
def evalChain (W : Opens X) (n : ℕ) (x : FullTerm U F n) :
    Chains (ι := ι) (n + 1) →+ F.obj.obj (op W) := by
  classical
  exact FreeAbelianGroup.lift fun a ↦
    if h : W ≤ CechSheafHZero.V U n a then F.obj.map (homOfLE h).op (x a) else 0

lemma evalChain_of (W : Opens X) (n : ℕ) (x : FullTerm U F n)
    (a : Fin (n + 1) → ι) (ha : W ≤ CechSheafHZero.V U n a) :
    evalChain U F W n x (FreeAbelianGroup.of a) = F.obj.map (homOfLE ha).op (x a) := by
  simp [evalChain, ha]

/-- Equality of additive evaluations can be checked on supported generators. -/
lemma supported_ext {A : Type*} [AddCommGroup A] (S : Set ι) (n : ℕ)
    (f g : Chains (ι := ι) n →+ A)
    (h : ∀ a : Fin n → ι, (∀ i, a i ∈ S) → f (.of a) = g (.of a))
    (z : Chains (ι := ι) n) (hz : z ∈ supported S n) : f z = g z := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz => obtain ⟨a, ha, rfl⟩ := hz; exact h a ha
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | neg x _ hx => simp only [map_neg, hx]

/-- Evaluation is additive in the section coordinates as well as in the chain. -/
def evalHom (W : Opens X) (n : ℕ) :
    FullTerm U F n →+ (Chains (ι := ι) (n + 1) →+ F.obj.obj (op W)) where
  toFun := evalChain U F W n
  map_zero' := by
    apply FreeAbelianGroup.lift_ext
    intro a
    simp [evalChain]
  map_add' x y := by
    apply FreeAbelianGroup.lift_ext
    intro a
    by_cases h : W ≤ CechSheafHZero.V U n a <;> simp [evalChain, h, map_add]

/-- Further restriction of an evaluation agrees on every supported chain. -/
lemma evalChain_restrict (W W' : Opens X) (h : W' ≤ W) (n : ℕ)
    (x : FullTerm U F n) (z : Chains (ι := ι) (n + 1))
    (hz : z ∈ supported (vertices U W) (n + 1)) :
    F.obj.map (homOfLE h).op (evalChain U F W n x z) = evalChain U F W' n x z := by
  apply supported_ext (vertices U W) (n + 1)
    ((F.obj.map (homOfLE h).op).hom.comp (evalChain U F W n x))
    (evalChain U F W' n x) _ z hz
  intro a ha
  change F.obj.map _ (evalChain U F W n x (.of a)) = evalChain U F W' n x (.of a)
  rw [evalChain_of _ _ _ _ _ _ (supported_le U W n a ha),
    evalChain_of _ _ _ _ _ _ (h.trans (supported_le U W n a ha))]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Coefficient morphisms act on all section coordinates. -/
def fullCoefficient {G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (n : ℕ) :
    FullTerm U F n →+ FullTerm U G n where
  toFun x a := f.hom.app (op (CechSheafHZero.V U n a)) (x a)
  map_zero' := by ext; exact map_zero _
  map_add' x y := by ext; exact map_add _ _ _

/-- Evaluation commutes with every coefficient morphism. -/
lemma evalChain_naturality {G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (W : Opens X) (n : ℕ) (x : FullTerm U F n) (z : Chains (ι := ι) (n + 1)) :
    evalChain U G W n (fullCoefficient U F f n x) z =
      f.hom.app (op W) (evalChain U F W n x z) := by
  have he : evalChain U G W n (fullCoefficient U F f n x) =
      (f.hom.app (op W)).hom.comp (evalChain U F W n x) := by
    apply FreeAbelianGroup.lift_ext
    intro a
    by_cases h : W ≤ CechSheafHZero.V U n a
    · simp only [evalChain, FreeAbelianGroup.lift_apply_of, dite_eq_left h,
        AddMonoidHom.comp_apply, fullCoefficient, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      exact (ConcreteCategory.congr_hom (f.hom.naturality (homOfLE h).op) (x a)).symm
    · simp [evalChain, h]
  exact DFunLike.congr_fun he z

/-- The full coordinate differential, expressed as the signed restriction sum. -/
def fullD (n : ℕ) : FullTerm U F n →+ FullTerm U F (n + 1) where
  toFun x a := ∑ k : Fin (n + 2), (-1 : ℤ) ^ k.val •
    F.obj.map (homOfLE (face_le U n a k)).op (x (a ∘ k.succAbove))
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [map_add, smul_add, Finset.sum_add_distrib]

/-- The coordinate differential is the differential of the full Cech complex. -/
lemma fullD_eq (n : ℕ) (x : (CechSheafHZero.C U F).X n) :
    fullD U F n (CechSheafHZero.termEquiv U F n x) =
      CechSheafHZero.termEquiv U F (n + 1) ((CechSheafHZero.C U F).d n (n + 1) x) := by
  funext a
  exact (full_differential U F n x a).symm

/-- Evaluating the boundary equals evaluating the section differential. -/
lemma evalChain_boundary (W : Opens X) (n : ℕ) (x : FullTerm U F n)
    (z : Chains (ι := ι) (n + 2)) (hz : z ∈ supported (vertices U W) (n + 2)) :
    evalChain U F W n x (boundary (n + 1) z) =
      evalChain U F W (n + 1) (fullD U F n x) z := by
  apply supported_ext (vertices U W) (n + 2)
    ((evalChain U F W n x).comp (boundary (n + 1)))
    (evalChain U F W (n + 1) (fullD U F n x)) _ z hz
  intro a ha
  change evalChain U F W n x (boundary (n + 1) (.of a)) = _
  rw [boundary_of, map_sum, evalChain_of _ _ _ _ _ _ (supported_le U W _ a ha)]
  change _ = F.obj.map _ (∑ k : Fin (n + 2), (-1 : ℤ) ^ k.val •
    F.obj.map (homOfLE (face_le U n a k)).op (x (a ∘ k.succAbove)))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_zsmul, map_zsmul]
  erw [evalChain_of U F W n x (a ∘ k.succAbove)
    (supported_le U W n _ (fun i ↦ ha (k.succAbove i)))]
  congr 1
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- A tuple generator is supported on the vertices containing its intersection. -/
lemma own_support (n : ℕ) (a : Fin (n + 1) → ι) :
    FreeAbelianGroup.of a ∈ supported (vertices U (CechSheafHZero.V U n a)) (n + 1) :=
  of_mem_supported _ _ a (fun i ↦ show CechSheafHZero.V U n a ≤ U (a i) from
    iInf_le _ i)

variable [LinearOrder ι]

/-- Evaluate the recursive integral homotopy in the actual dependent section groups. -/
def homotopyCoordinate (n : ℕ) : FullTerm U F (n + 1) →+ FullTerm U F n where
  toFun x a := evalChain U F (CechSheafHZero.V U n a) (n + 1) x (H (n + 1) (.of a))
  map_zero' := by
    funext a
    exact DFunLike.congr_fun (map_zero (evalHom U F _ _)) _
  map_add' x y := by
    funext a
    exact DFunLike.congr_fun (map_add (evalHom U F _ _) x y) _

/-- Every chain used by the homotopy has the required geometric support. -/
lemma homotopy_supported (n : ℕ) (a : Fin (n + 1) → ι) :
    H (n + 1) (.of a) ∈ supported (vertices U (CechSheafHZero.V U n a)) (n + 2) :=
  H_mem_supported _ _ _ (own_support U n a)

/-- The section homotopy commutes with coefficient morphisms. -/
lemma homotopyCoordinate_naturality {G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (n : ℕ) (x : FullTerm U F (n + 1)) :
    homotopyCoordinate U G n (fullCoefficient U F f (n + 1) x) =
      fullCoefficient U F f n (homotopyCoordinate U F n x) := by
  funext a
  exact evalChain_naturality U F f _ _ x _

/-- Degree zero of the section homotopy vanishes. -/
lemma homotopyCoordinate_zero (x : FullTerm U F 1) : homotopyCoordinate U F 0 x = 0 := by
  funext a
  change evalChain U F _ _ x (H 1 (.of a)) = 0
  rw [H_one, map_zero]

/-- Restricting a homotopy coordinate evaluates the same supported chain. -/
lemma homotopyCoordinate_restrict (n : ℕ) (x : FullTerm U F (n + 1))
    (a : Fin (n + 1) → ι) (W : Opens X) (h : W ≤ CechSheafHZero.V U n a) :
    F.obj.map (homOfLE h).op (homotopyCoordinate U F n x a) =
      evalChain U F W (n + 1) x (H (n + 1) (.of a)) :=
  evalChain_restrict U F _ W h _ x _ (homotopy_supported U n a)

omit [LinearOrder ι] in
/-- Evaluation at a tuple's own intersection is its section coordinate. -/
lemma evalChain_self (n : ℕ) (x : FullTerm U F n) (a : Fin (n + 1) → ι) :
    evalChain U F (CechSheafHZero.V U n a) n x (.of a) = x a := by
  rw [evalChain_of _ _ _ _ _ _ le_rfl]
  change F.obj.map (𝟙 _) (x a) = x a
  rw [F.obj.map_id]
  rfl

/-- Integral sorting evaluates as the sorting-restriction composite on sections. -/
lemma evalChain_P (n : ℕ) (x : FullTerm U F n) (a : Fin (n + 1) → ι) :
    evalChain U F (CechSheafHZero.V U n a) n x (P (n + 1) (.of a)) =
      CechSortingMaps.sortingHom U F n (restrict U F n x) a := by
  change _ = signedSort U F n (restrict U F n x) a
  rw [P_of]
  by_cases ha : Function.Injective a
  · rw [signedGenerator_of_injective a ha, map_zsmul,
      evalChain_of _ _ _ _ _ _ (perm_le U a (Tuple.sort a)),
      signedSort_of_injective U F n _ a ha]
    rfl
  · rw [signedGenerator_of_not_injective a ha, map_zero,
      signedSort_of_not_injective U F n _ a ha]

/-- The differential of the section homotopy evaluates the homotopy of the boundary. -/
lemma fullD_homotopyCoordinate (n : ℕ) (x : FullTerm U F (n + 1))
    (a : Fin (n + 2) → ι) :
    fullD U F n (homotopyCoordinate U F n x) a =
      evalChain U F (CechSheafHZero.V U (n + 1) a) (n + 1) x
        (H (n + 1) (boundary (n + 1) (.of a))) := by
  rw [boundary_of, map_sum, map_sum]
  change (∑ k : Fin (n + 2), (-1 : ℤ) ^ k.val •
    F.obj.map (homOfLE (face_le U n a k)).op
      (homotopyCoordinate U F n x (a ∘ k.succAbove))) = _
  apply Finset.sum_congr rfl
  intro k _
  rw [map_zsmul, map_zsmul, homotopyCoordinate_restrict]

/-- The coordinate homotopy equation in every positive degree. -/
lemma homotopyCoordinate_equation (n : ℕ) (x : FullTerm U F (n + 1)) :
    fullD U F n (homotopyCoordinate U F n x) +
        homotopyCoordinate U F (n + 1) (fullD U F (n + 1) x) =
      x - CechSortingMaps.sortingHom U F (n + 1) (restrict U F (n + 1) x) := by
  funext a
  have he := congrArg (evalChain U F (CechSheafHZero.V U (n + 1) a) (n + 1) x)
    (boundary_H_add_H_boundary (n + 1) (FreeAbelianGroup.of a))
  rw [map_add, map_sub, evalChain_self, evalChain_P,
    evalChain_boundary _ _ _ _ _ _ (homotopy_supported U (n + 1) a)] at he
  change fullD U F n (homotopyCoordinate U F n x) a +
    evalChain U F _ _ (fullD U F (n + 1) x) (H (n + 2) (.of a)) = _
  rw [fullD_homotopyCoordinate]
  exact (add_comm _ _).trans he

/-- The degree-zero equation has no incoming differential term. -/
lemma homotopyCoordinate_equation_zero (x : FullTerm U F 0) :
    homotopyCoordinate U F 0 (fullD U F 0 x) =
      x - CechSortingMaps.sortingHom U F 0 (restrict U F 0 x) := by
  rw [homotopyCoordinate_zero]
  funext a
  have he := evalChain_P U F 0 x a
  rw [P_one, evalChain_self] at he
  exact (sub_eq_zero.mpr he).symm

end FLT.Mazur.CechSortingHomotopyEvaluation
