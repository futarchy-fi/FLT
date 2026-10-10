/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.TensorOpenChart
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Separating tensor charts by a vanishing base parameter

If every original intersection lies away from a parameter, extending to a
coefficient algebra where that parameter vanishes makes the intersection empty.
The older scheme need not be affine.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.TensorOpenChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] {X U : Scheme.{u}}
  (base : X ⟶ Spec (.of R)) (i : U ⟶ X) (j : Spec (.of A) ⟶ X)
  (hj : j ≫ base = Spec.map (CommRingCat.ofHom (algebraMap R A)))
  (π : R) (hπ : algebraMap R S π = 0)
  (h : ∀ (a : U) (c : Spec (.of A)), i a = j c → π ∉ (base (j c)).asIdeal)
local notation "p" => pullback.snd
  (Spec.map (CommRingCat.ofHom (algebraMap R S))) base
local notation "old" => pullback.snd i p
local notation "new" => chart (S := S) base j hj

include hπ h in
/-- The base-changed older scheme and actual tensor chart have no common point. -/
theorem vanishing_disjoint : Disjoint (Set.range old) (Set.range new) := by
  rw [Set.disjoint_left]
  rintro _ ⟨a, rfl⟩ ⟨c, hc⟩
  have he : i (pullback.fst i p a) = j (projection c) := by
    have hp := congrArg (fun g => g a) (pullback.condition (f := i) (g := p))
    have hn := congrArg (fun g => g c) (chart_snd base j hj)
    exact hp.trans ((congrArg p hc).symm.trans hn)
  apply h (pullback.fst i p a) (projection c) he
  have hb : base (j (projection c)) =
      Spec.map (CommRingCat.ofHom (algebraMap R S))
        (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S))) base (new c)) := by
    have hn := congrArg (fun g => base (g c)) (chart_snd base j hj)
    have hp := congrArg (fun g => g (new c))
      (pullback.condition (f := Spec.map (CommRingCat.ofHom (algebraMap R S))) (g := base))
    exact hn.symm.trans hp.symm
  rw [hb]
  change algebraMap R S π ∈
    (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S))) base (new c)).asIdeal
  rw [hπ]
  exact Ideal.zero_mem _

include hπ h in
/-- The full scheme intersection is empty, without a reducedness assumption. -/
theorem vanishing_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) old new := by
  let _ := Scheme.isEmpty_pullback old new (vanishing_disjoint base i j hj π hπ h)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback old new)))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

end FLT.Mazur.TensorOpenChart
