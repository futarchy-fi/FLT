/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FilteredComplexDescent

/-!
# Cohomology classes in a filtered union

Classes have finite-stage representatives, and a class that vanishes in the
union vanishes at a later stage. The bounding cochain is constructed by descent.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open CategoryTheory Limits HomologicalComplex

variable {k : Type u} [CommRing k] {J : Type u} [SmallCategory J]
  (F : J ⥤ CochainComplex (ModuleCat.{u} k) ℕ) (c : Cocone F)
  (hinj : ∀ i n, Function.Injective ((c.ι.app i).f n).hom)
  (hsurj : ∀ n (x : c.pt.X n), ∃ i y, ((c.ι.app i).f n).hom y = x)

include hinj hsurj

/-- Every class in the union has a finite-stage representative. -/
theorem complexCocone_homology_surjective (n : ℕ) (x : c.pt.homology n) :
    ∃ i y, (homologyMap (c.ι.app i) n).hom y = x := by
  obtain ⟨z, hz, rfl⟩ := cochainHomologyClass_surjective c.pt n x
  obtain ⟨i, w, rfl⟩ := hsurj n z
  have hw := complexCocone_cycle F c hinj i n _ w hz
  exact ⟨i, cochainHomologyClass (F.obj i) n w hw,
    cochainHomologyClass_map (F.obj i) n (c.ι.app i) w hw hz⟩

variable [IsFiltered J]

/-- A class zero in the union is zero after an actual refinement. -/
theorem complexCocone_homology_zero (n : ℕ) (i : J) (x : (F.obj i).homology n)
    (hx : (homologyMap (c.ι.app i) n).hom x = 0) :
    ∃ (j : J) (f : i ⟶ j), (homologyMap (F.map f) n).hom x = 0 := by
  obtain ⟨z, hz, rfl⟩ := cochainHomologyClass_surjective (F.obj i) n x
  have hz' := cochainMap_cycle (F.obj i) n (c.ι.app i) _ z hz
  rw [cochainHomologyClass_map _ _ _ _ _ hz', cochainHomologyClass_eq_zero_iff] at hx
  obtain ⟨b, hb⟩ := hx
  obtain ⟨j, f, b', hb'⟩ := complexCocone_boundary F c hinj hsurj i _ n z b hb
  have hfz := cochainMap_cycle (F.obj i) n (F.map f) _ z hz
  refine ⟨j, f, ?_⟩
  rw [cochainHomologyClass_map _ _ _ _ _ hfz, cochainHomologyClass_eq_zero_iff]
  exact ⟨b', hb'⟩

/-- Two classes with equal images become equal at some later stage. -/
theorem complexCocone_homology_eq (n : ℕ) (i : J) (x y : (F.obj i).homology n)
    (h : (homologyMap (c.ι.app i) n).hom x = (homologyMap (c.ι.app i) n).hom y) :
    ∃ (j : J) (f : i ⟶ j),
      (homologyMap (F.map f) n).hom x = (homologyMap (F.map f) n).hom y := by
  obtain ⟨j, f, hf⟩ := complexCocone_homology_zero F c hinj hsurj n i (x - y)
    (by rw [map_sub, h, sub_self])
  exact ⟨j, f, sub_eq_zero.mp (by simpa only [map_sub] using hf)⟩

end LocalClassFieldTheory
