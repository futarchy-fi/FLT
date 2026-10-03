/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CochainHomologyClass
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Cocycles and boundaries in a filtered union of complexes

Injective structure maps detect cocycles. A bounding cochain descends to a
stage, and filteredness supplies a common refinement with the original cocycle.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open CategoryTheory Limits HomologicalComplex

variable {k : Type u} [CommRing k] {J : Type u} [SmallCategory J]
  (F : J ⥤ CochainComplex (ModuleCat.{u} k) ℕ) (c : Cocone F)

/-- Componentwise naturality of a cocone of complexes. -/
theorem complexCocone_naturality {i j : J} (f : i ⟶ j) (n : ℕ) (x : (F.obj i).X n) :
    ((c.ι.app j).f n).hom (((F.map f).f n).hom x) = ((c.ι.app i).f n).hom x :=
  congrArg (fun g => (g.f n).hom x) (c.w f)

/-- Injective inflation reflects the cocycle equation, in any degree. -/
theorem complexCocone_cycle (hinj : ∀ i n, Function.Injective ((c.ι.app i).f n).hom)
    (i : J) (n m : ℕ) (x : (F.obj i).X n)
    (hx : (c.pt.d n m).hom (((c.ι.app i).f n).hom x) = 0) :
    ((F.obj i).d n m).hom x = 0 := by
  apply hinj i m
  rw [map_zero]
  exact (congrArg (fun g => g.hom x) ((c.ι.app i).comm n m).symm).trans hx

variable [IsFiltered J]

/-- A boundary in the union is already a boundary at some common refinement. -/
theorem complexCocone_boundary
    (hinj : ∀ i n, Function.Injective ((c.ι.app i).f n).hom)
    (hsurj : ∀ n (x : c.pt.X n), ∃ i y, ((c.ι.app i).f n).hom y = x)
    (i : J) (n m : ℕ) (x : (F.obj i).X m)
    (b : c.pt.X n) (hb : (c.pt.d n m).hom b = ((c.ι.app i).f m).hom x) :
    ∃ (j : J) (f : i ⟶ j) (b' : (F.obj j).X n),
      ((F.obj j).d n m).hom b' = ((F.map f).f m).hom x := by
  obtain ⟨l, b₀, hb₀⟩ := hsurj n b
  let j := IsFiltered.max i l
  let f : i ⟶ j := IsFiltered.leftToMax i l
  let g : l ⟶ j := IsFiltered.rightToMax i l
  refine ⟨j, f, ((F.map g).f n).hom b₀, ?_⟩
  apply hinj j m
  calc
    _ = (c.pt.d n m).hom (((c.ι.app j).f n).hom (((F.map g).f n).hom b₀)) :=
      congrArg (fun h => h.hom (((F.map g).f n).hom b₀)) ((c.ι.app j).comm n m).symm
    _ = (c.pt.d n m).hom b := by rw [complexCocone_naturality, hb₀]
    _ = ((c.ι.app i).f m).hom x := hb
    _ = _ := (complexCocone_naturality F c f m x).symm

end LocalClassFieldTheory
