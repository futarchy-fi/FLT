/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FilteredRingFiniteUnits

/-!
# Simultaneous witnesses in the base and algebra coefficient systems

Flatness witnesses involve equations in two rings. Lift both finite
families above a prescribed stage, then detect both families of equations
after one common transition. Neither transition is assumed injective.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace FLT.Mazur.Approximation
universe u v w
variable {I : Type v} [Category.{w} I] [IsFiltered I]
  (F G : I ⥤ CommRingCat.{u}) (c : Cocone F) (d : Cocone G)
  (hc : IsColimit c) (hd : IsColimit d)
  [PreservesColimit F (forget CommRingCat)]
  [PreservesColimit G (forget CommRingCat)]

include hc hd in
/-- Base coefficients and algebra elements lift together above any fixed model stage. -/
theorem exists_pair_element_lifts {K L : Type*} [Finite K] [Finite L]
    (i : I) (x : K → c.pt) (y : L → d.pt) :
    ∃ (j : I) (_ : i ⟶ j) (a : K → F.obj j) (b : L → G.obj j),
      (∀ k, c.ι.app j (a k) = x k) ∧ ∀ l, d.ι.app j (b l) = y l := by
  obtain ⟨j, f, a, ha⟩ := exists_lifts_of_finite F c hc i x
  obtain ⟨k, g, b, hb⟩ := exists_lifts_of_finite G d hd j y
  refine ⟨k, f ≫ g, fun t ↦ F.map g (a t), b, fun t ↦ ?_, hb⟩
  exact (congrArg (fun q : F.obj j ⟶ c.pt ↦ q (a t)) (c.w g)).trans (ha t)

include hc hd in
/-- Equations in the two rings hold after one common transition from their source stage. -/
theorem exists_pair_map_eq {K L : Type*} [Finite K] [Finite L]
    (i : I) (a b : K → F.obj i) (x y : L → G.obj i)
    (h : ∀ k, c.ι.app i (a k) = c.ι.app i (b k))
    (h' : ∀ l, d.ι.app i (x l) = d.ι.app i (y l)) :
    ∃ (j : I) (f : i ⟶ j),
      (∀ k, F.map f (a k) = F.map f (b k)) ∧
      ∀ l, G.map f (x l) = G.map f (y l) := by
  obtain ⟨j, f, hf⟩ := exists_map_eq_of_finite F c hc i a b h
  have hj (l : L) : d.ι.app j (G.map f (x l)) = d.ι.app j (G.map f (y l)) := by
    have hx := congrArg (fun q : G.obj i ⟶ d.pt ↦ q (x l)) (d.w f)
    have hy := congrArg (fun q : G.obj i ⟶ d.pt ↦ q (y l)) (d.w f)
    exact hx.trans ((h' l).trans hy.symm)
  obtain ⟨k, g, hg⟩ := exists_map_eq_of_finite G d hd j
    (fun l ↦ G.map f (x l)) (fun l ↦ G.map f (y l)) hj
  refine ⟨k, f ≫ g, fun t ↦ ?_, fun l ↦ ?_⟩
  · rw [F.map_comp]
    exact congrArg (F.map g) (hf t)
  · rw [G.map_comp]
    exact hg l

end FLT.Mazur.Approximation
