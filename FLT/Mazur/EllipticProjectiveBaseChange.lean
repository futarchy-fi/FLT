/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticProjectiveReduction

/-!
# Base change of actual projective point groups

Coordinate extension gives an additive map on the actual nonsingular point
groups. The target equation is explicit, allowing compatible integral models
to be used without transporting projective representatives through casts.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve WeierstrassCurve.Projective

variable {K L : Type*} [Field K] [Field L]

/-- Extend coefficients of a projective class along a field homomorphism. -/
def extensionPointClass (f : K →+* L) : PointClass K → PointClass L :=
  Quotient.map (fun v => f ∘ v) fun _ _ h => by
    obtain ⟨u, rfl⟩ := h
    exact ⟨Units.map f u, (comp_smul ..).symm⟩

/-- Coordinate extension preserves and reflects nonsingularity. -/
theorem extensionPointClass_nonsingular (W : WeierstrassCurve K) (f : K →+* L)
    (P : PointClass K) :
    (W.map f).toProjective.NonsingularLift (extensionPointClass f P) ↔
      W.toProjective.NonsingularLift P := by
  induction P using Quotient.inductionOn with | _ v =>
    exact W.toProjective.map_nonsingular f.injective v

/-- The point-group homomorphism induced by a compatible field extension. -/
noncomputable def extensionProjectiveHom (W : WeierstrassCurve K) (f : K →+* L)
    (V : WeierstrassCurve L) (he : W.map f = V) : W.toProjective.Point →+ V.toProjective.Point := by
  classical
  refine
    { toFun := fun P =>
        { point := extensionPointClass f P.point
          nonsingular := by
            rw [← he]
            exact (extensionPointClass_nonsingular W f P.point).mpr P.nonsingular }
      map_zero' := ?_
      map_add' := ?_ }
  · apply Point.ext
    change (⟦f ∘ ![0, 1, 0]⟧ : PointClass L) = ⟦![0, 1, 0]⟧
    simp only [comp_fin3, map_zero, map_one]
  · intro P Q
    apply Point.ext
    change extensionPointClass f (W.toProjective.addMap P.point Q.point) =
      V.toProjective.addMap (extensionPointClass f P.point) (extensionPointClass f Q.point)
    obtain ⟨p, hp⟩ := Quotient.exists_rep P.point
    obtain ⟨q, hq⟩ := Quotient.exists_rep Q.point
    have hpn : W.toProjective.Nonsingular p := by
      have h := P.nonsingular
      rw [← hp] at h
      exact h
    have hqn : W.toProjective.Nonsingular q := by
      have h := Q.nonsingular
      rw [← hq] at h
      exact h
    rw [← hp, ← hq, ← he]
    change (⟦f ∘ W.toProjective.add p q⟧ : PointClass L) =
      ⟦(W.map f).toProjective.add (f ∘ p) (f ∘ q)⟧
    rw [Projective.map_add f hpn hqn]

/-- The point homomorphism is represented by coefficient extension. -/
theorem extensionProjectiveHom_point (W : WeierstrassCurve K) (f : K →+* L)
    (V : WeierstrassCurve L) (he : W.map f = V) (P : W.toProjective.Point) :
    (extensionProjectiveHom W f V he P).point = extensionPointClass f P.point := rfl

end FLT.Mazur
