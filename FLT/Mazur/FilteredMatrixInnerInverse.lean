/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FilteredRingFiniteUnits
public import Mathlib.Data.Matrix.Mul

/-!
# Descending a finite matrix inner inverse

The entries of an inner inverse and its defining equation descend to one
actual filtered stage above the given matrix. No injectivity or flatness of
the transition maps is needed.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace FLT.Mazur.Approximation
universe u v w
variable {I : Type v} [Category.{w} I] [IsFiltered I]
  (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
  [PreservesColimit F (forget CommRingCat)]
  {m n : Type*} [Fintype m] [Fintype n]

include hc in
/-- A matrix that acquires an inner inverse at the colimit has one at a later stage. -/
theorem exists_matrix_innerInverse_stage (i : I) (A : Matrix m n (F.obj i))
    (B : Matrix n m c.pt)
    (h : let A₀ : Matrix m n c.pt := A.map (c.ι.app i).hom
      A₀ * B * A₀ = A₀) :
    ∃ (j : I) (g : i ⟶ j) (D : Matrix n m (F.obj j)),
      A.map (F.map g).hom * D * A.map (F.map g).hom = A.map (F.map g).hom := by
  obtain ⟨j, g, b, hb⟩ := exists_lifts_of_finite F c hc i (fun t : n × m ↦ B t.1 t.2)
  let A' := A.map (F.map g).hom
  let B' : Matrix n m (F.obj j) := fun x y ↦ b (x, y)
  have ha : A'.map (c.ι.app j).hom = A.map (c.ι.app i).hom := by
    ext x y
    exact congrArg (fun q : F.obj i ⟶ c.pt ↦ q (A x y)) (c.w g)
  have hb' : B'.map (c.ι.app j).hom = B := by
    ext x y
    exact hb (x, y)
  have he : (A' * B' * A').map (c.ι.app j).hom = A'.map (c.ι.app j).hom := by
    simpa only [Matrix.map_mul, ha, hb'] using h
  obtain ⟨k, e, he'⟩ := exists_map_eq_of_finite F c hc j
    (fun t : m × n ↦ (A' * B' * A') t.1 t.2)
    (fun t : m × n ↦ A' t.1 t.2) (fun t ↦ congrFun (congrFun he t.1) t.2)
  have heq : (A' * B' * A').map (F.map e).hom = A'.map (F.map e).hom := by
    ext x y
    exact he' (x, y)
  have hae : A'.map (F.map e).hom = A.map (F.map (g ≫ e)).hom := by
    ext x y
    change F.map e (F.map g (A x y)) = F.map (g ≫ e) (A x y)
    rw [F.map_comp]
    rfl
  refine ⟨k, g ≫ e, B'.map (F.map e).hom, ?_⟩
  simpa only [Matrix.map_mul, hae] using heq

end FLT.Mazur.Approximation
