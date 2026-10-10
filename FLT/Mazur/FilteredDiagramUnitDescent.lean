/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FilteredRingFamilyDescent
public import Mathlib.CategoryTheory.FinCategory.Basic
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Basic.Finite.Sigma

/-!
# Unit cocycles descend through filtered ring diagrams

Lift a finite family of units, then impose every restriction and multiplication
equation at one common refinement. No presentation of the limit rings is needed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace FLT.Mazur.Approximation

universe u v w

variable {I : Type v} [Category.{w} I] [IsFiltered I]
  {J : Type*} [SmallCategory J] [FinCategory J]
  (F : J → I ⥤ CommRingCat.{u}) (c : ∀ j, Cocone (F j))
  (hc : ∀ j, IsColimit (c j))
  [∀ j, PreservesColimit (F j) (forget CommRingCat)]

include hc in
/-- Lift genuine units together with all finite naturality and cocycle equations. -/
theorem exists_filtered_diagram_units
    (φ : ∀ {j k}, (j ⟶ k) → (F j ⟶ F k))
    (ψ : ∀ {j k}, (j ⟶ k) → ((c j).pt ⟶ (c k).pt))
    (hφ : ∀ {j k} (f : j ⟶ k) i,
      (φ f).app i ≫ (c k).ι.app i = (c j).ι.app i ≫ ψ f)
    (K L : J → Type*) [∀ j, Finite (K j)] [∀ j, Finite (L j)]
    (x : ∀ j, K j → (c j).ptˣ) (τ : ∀ {j k}, (j ⟶ k) → K j → K k)
    (hx : ∀ {j k} (f : j ⟶ k) a, ψ f (x j a) = (x k (τ f a) : (c k).pt))
    (a b d : ∀ j, L j → K j)
    (hmul : ∀ j l, x j (a j l) * x j (b j l) = x j (d j l)) (i : I) :
    ∃ (s : I) (_ : i ⟶ s) (y : ∀ j, K j → ((F j).obj s)ˣ),
      (∀ j k, Units.map ((c j).ι.app s).hom.toMonoidHom (y j k) = x j k) ∧
      (∀ {j k} (f : j ⟶ k) l,
        (φ f).app s (y j l) = (y k (τ f l) : (F k).obj s)) ∧
      ∀ j l, y j (a j l) * y j (b j l) = y j (d j l) := by
  classical
  obtain ⟨r, f, y, hy⟩ := exists_family_unit_lifts F c hc K i x
  let T (k : J) := (Σ j : J, (j ⟶ k) × K j) ⊕ L k
  let _ (k : J) : Finite (T k) := by
    dsimp [T]
    infer_instance
  let v : ∀ k, T k → (F k).obj r := fun k ↦ Sum.elim
    (fun ⟨_, g, l⟩ ↦ (φ g).app r (y _ l))
    (fun l ↦ (y k (a k l) : (F k).obj r) * y k (b k l))
  let z : ∀ k, T k → (F k).obj r := fun k ↦ Sum.elim
    (fun ⟨_, g, l⟩ ↦ y k (τ g l)) (fun l ↦ y k (d k l))
  have hy' j k : (c j).ι.app r (y j k) = (x j k : (c j).pt) :=
    congrArg Units.val (hy j k)
  have hvz (k : J) (t : T k) : (c k).ι.app r (v k t) = (c k).ι.app r (z k t) := by
    rcases t with ⟨j, g, l⟩ | l
    · change (c k).ι.app r ((φ g).app r (y j l)) = (c k).ι.app r (y k (τ g l))
      have he := congrArg (fun q : (F j).obj r ⟶ (c k).pt ↦ q (y j l)) (hφ g r)
      exact he.trans (by simp only [CommRingCat.comp_apply, hy']; exact hx g l)
    · change (c k).ι.app r ((y k (a k l) : (F k).obj r) * y k (b k l)) =
        (c k).ι.app r (y k (d k l))
      rw [map_mul, hy', hy', hy']
      exact congrArg Units.val (hmul k l)
  obtain ⟨s, g, hg⟩ := exists_family_map_eq F c hc T r v z hvz
  let w : ∀ j, K j → ((F j).obj s)ˣ :=
    fun j k ↦ Units.map ((F j).map g).hom.toMonoidHom (y j k)
  refine ⟨s, f ≫ g, w, ?_, ?_, ?_⟩
  · intro j k
    apply Units.ext
    change (c j).ι.app s ((F j).map g (y j k)) = (x j k : (c j).pt)
    exact (congrArg (fun q : (F j).obj r ⟶ (c j).pt ↦ q (y j k))
      ((c j).w g)).trans (hy' j k)
  · intro j k h l
    change (φ h).app s ((F j).map g (y j l)) = (F k).map g (y k (τ h l))
    have he := congrArg (fun q : (F j).obj r ⟶ (F k).obj s ↦ q (y j l))
      ((φ h).naturality g)
    exact he.trans (hg k (.inl ⟨j, h, l⟩))
  · intro j l
    apply Units.ext
    change (F j).map g (y j (a j l)) * (F j).map g (y j (b j l)) =
      (F j).map g (y j (d j l))
    simpa only [v, z, Sum.elim_inr, map_mul] using hg j (.inr l)

end FLT.Mazur.Approximation
