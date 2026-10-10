/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FilteredRingFamilyElements
public import FLT.Mazur.FilteredDiagramUnitDescent

/-!
# Descent of section coordinates with fixed transition coefficients

Finite compatible coordinates in filtered ring colimits descend together.
Equations with coefficients at the prescribed stage are imposed by equality
detection; this applies to the transition units of any chosen tensor power.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

namespace FLT.Mazur.Approximation

universe u v w

variable {I : Type v} [Category.{w} I] [IsFiltered I]
  {J : Type*} [SmallCategory J] [FinCategory J]
  (F : J → I ⥤ CommRingCat.{u}) (c : ∀ j, Cocone (F j))
  (hc : ∀ j, IsColimit (c j))
  [∀ j, PreservesColimit (F j) (forget CommRingCat)]

include hc in
/-- Lift finite coordinates, retaining restrictions and all fixed-coefficient equations. -/
theorem exists_filtered_diagram_sections
    (φ : ∀ {j k}, (j ⟶ k) → (F j ⟶ F k))
    (ψ : ∀ {j k}, (j ⟶ k) → ((c j).pt ⟶ (c k).pt))
    (hφ : ∀ {j k} (f : j ⟶ k) i,
      (φ f).app i ≫ (c k).ι.app i = (c j).ι.app i ≫ ψ f)
    (K L : J → Type*) [∀ j, Finite (K j)] [∀ j, Finite (L j)]
    (x : ∀ j, K j → (c j).pt) (τ : ∀ {j k}, (j ⟶ k) → K j → K k)
    (hx : ∀ {j k} (f : j ⟶ k) a, ψ f (x j a) = x k (τ f a))
    (i : I) (a b : ∀ j, L j → K j) (u : ∀ j, L j → (F j).obj i)
    (hu : ∀ j l, x j (a j l) =
      @HMul.hMul (c j).pt (c j).pt (c j).pt inferInstance
        ((c j).ι.app i (u j l)) (x j (b j l))) :
    ∃ (s : I) (h : i ⟶ s) (y : ∀ j, K j → (F j).obj s),
      (∀ j k, (c j).ι.app s (y j k) = x j k) ∧
      (∀ {j k} (f : j ⟶ k) l, (φ f).app s (y j l) = y k (τ f l)) ∧
      ∀ j l, y j (a j l) = (F j).map h (u j l) * y j (b j l) := by
  classical
  obtain ⟨r, f, y, hy⟩ := exists_family_element_lifts F c hc K i x
  let T (k : J) := (Σ j : J, (j ⟶ k) × K j) ⊕ L k
  let _ (k : J) : Finite (T k) := by
    dsimp [T]
    infer_instance
  let v : ∀ k, T k → (F k).obj r := fun k ↦ Sum.elim
    (fun ⟨_, g, l⟩ ↦ (φ g).app r (y _ l)) (fun l ↦ y k (a k l))
  let z : ∀ k, T k → (F k).obj r := fun k ↦ Sum.elim
    (fun ⟨_, g, l⟩ ↦ y k (τ g l))
    (fun l ↦ (F k).map f (u k l) * y k (b k l))
  have hvz (k : J) (t : T k) : (c k).ι.app r (v k t) = (c k).ι.app r (z k t) := by
    rcases t with ⟨j, g, l⟩ | l
    · change (c k).ι.app r ((φ g).app r (y j l)) = (c k).ι.app r (y k (τ g l))
      have he := congrArg (fun q : (F j).obj r ⟶ (c k).pt ↦ q (y j l)) (hφ g r)
      exact he.trans (by simp only [CommRingCat.comp_apply, hy]; exact hx g l)
    · change (c k).ι.app r (y k (a k l)) =
        (c k).ι.app r ((F k).map f (u k l) * y k (b k l))
      rw [map_mul, hy, hy]
      have he := congrArg (fun q : (F k).obj i ⟶ (c k).pt ↦ q (u k l)) ((c k).w f)
      exact (hu k l).trans (congrArg (fun t ↦ t * x k (b k l)) he.symm)
  obtain ⟨s, g, hg⟩ := exists_family_map_eq F c hc T r v z hvz
  refine ⟨s, f ≫ g, fun j k ↦ (F j).map g (y j k), ?_, ?_, ?_⟩
  · intro j k
    exact (congrArg (fun q : (F j).obj r ⟶ (c j).pt ↦ q (y j k))
      ((c j).w g)).trans (hy j k)
  · intro j k h l
    have he := congrArg (fun q : (F j).obj r ⟶ (F k).obj s ↦ q (y j l))
      ((φ h).naturality g)
    exact he.trans (hg k (.inl ⟨j, h, l⟩))
  · intro j l
    simpa only [v, z, Sum.elim_inr, map_mul, Functor.map_comp, CommRingCat.comp_apply]
      using hg j (.inr l)

end FLT.Mazur.Approximation
