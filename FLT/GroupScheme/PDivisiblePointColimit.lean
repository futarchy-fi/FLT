/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleSystem
public import Mathlib.Order.DirectedInverseSystem

/-! # The pointwise colimit of the original finite-flat levels

This constructs a functor of sets. No sheaf or formal representability is asserted.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)
  {B C D : Type} [CommRing B] [CommRing C] [CommRing D]
  [Algebra R B] [Algebra R C] [Algebra R D]

/-- Transition of test-algebra points along the original closed inclusion. -/
def pointInclusion {m n : ℕ} (h : m ≤ n) :
    ((X.level m).CoordinateRing →ₐ[R] B) ↪ ((X.level n).CoordinateRing →ₐ[R] B) where
  toFun x := x.comp (X.inclusion h).toAlgHom
  inj' := by
    intro x y hxy
    ext a
    obtain ⟨b, rfl⟩ := X.closed h a
    exact AlgHom.congr_fun hxy b

instance pointDirectedSystem :
    DirectedSystem (fun n ↦ (X.level n).CoordinateRing →ₐ[R] B)
      (fun _ _ h ↦ X.pointInclusion (B := B) h) where
  map_self := by intro i x; simp [pointInclusion, X.inclusion_refl]
  map_map := by
    intro k j i h l x
    change (x.comp (X.inclusion h).toAlgHom).comp (X.inclusion l).toAlgHom = _
    rw [AlgHom.comp_assoc]
    exact congrArg (fun f ↦ x.comp (BialgHom.toAlgHom f)) (X.inclusion_comp h l)

/-- The pointwise filtered colimit with the specified integral inclusion maps. -/
abbrev PointColimit (B : Type) [CommRing B] [Algebra R B] :=
  DirectLimit (fun n ↦ (X.level n).CoordinateRing →ₐ[R] B)
    (fun _ _ h ↦ X.pointInclusion (B := B) h)

/-- The original level point as a colimit point. -/
def pointColimitMk (n : ℕ) (x : (X.level n).CoordinateRing →ₐ[R] B) :
    X.PointColimit B := ⟦⟨n, x⟩⟧

/-- Original inclusions preserve the represented colimit point. -/
theorem pointColimitMk_inclusion {m n : ℕ} (h : m ≤ n)
    (x : (X.level m).CoordinateRing →ₐ[R] B) :
    X.pointColimitMk n (X.pointInclusion h x) = X.pointColimitMk m x :=
  Quotient.sound ⟨n, le_rfl, h, by
    change (X.pointInclusion h x).comp (X.inclusion le_rfl).toAlgHom = _
    rw [X.inclusion_refl]
    rfl⟩

/-- Closedness makes every original level embed in the colimit. -/
theorem pointColimitMk_injective (n : ℕ) :
    Function.Injective (X.pointColimitMk (B := B) n) :=
  DirectLimit.mk_injective (fun _ _ h ↦ X.pointInclusion (B := B) h)
    (fun _ _ h ↦ (X.pointInclusion h).injective) n

/-- A test-algebra map acts on the colimit by postcomposition at each original level. -/
def pointColimitMap (q : B →ₐ[R] C) : X.PointColimit B → X.PointColimit C :=
  DirectLimit.map _ _ (fun _ x ↦ q.comp x) (fun _ _ _ _ ↦ rfl)

/-- Evaluation of the functor map on an original point. -/
theorem pointColimitMap_mk (q : B →ₐ[R] C) (n : ℕ)
    (x : (X.level n).CoordinateRing →ₐ[R] B) :
    X.pointColimitMap q (X.pointColimitMk n x) = X.pointColimitMk n (q.comp x) := rfl

/-- The identity test-algebra map acts identically. -/
theorem pointColimitMap_id (x : X.PointColimit B) :
    X.pointColimitMap (AlgHom.id R B) x = x := by
  induction x using Quotient.ind with | _ x => rfl

/-- Test-algebra composition is preserved. -/
theorem pointColimitMap_comp (q : B →ₐ[R] C) (s : C →ₐ[R] D) (x : X.PointColimit B) :
    X.pointColimitMap (s.comp q) x = X.pointColimitMap s (X.pointColimitMap q x) := by
  induction x using Quotient.ind with | _ x => rfl

end ThreeAdicPlan.PDivisibleSystem
