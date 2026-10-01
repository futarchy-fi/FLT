/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonNodePresentation
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# The affine algebra of pinching two points

The one-gon chart is the pullback of evaluation at zero and one along the
diagonal. We give the universal property for arbitrary commutative source
rings, not just coefficient-algebra homomorphisms. Evaluation is surjective
and its kernel is the conductor ideal. This is ring algebra; descent to
arbitrary target schemes still needs a separate proof.
-/

@[expose] public noncomputable section

open Polynomial
open FLT.Mazur.PolygonNodePresentation

namespace FLT.Mazur.OneGonPinchingAlgebra

variable {R : Type*} [CommRing R]

/-- Restriction to the two points of the normalization being identified. -/
def endpoints : R[X] →+* R × R :=
  (evalRingHom 0).prod (evalRingHom 1)

/-- Functions on the pinched point pull back to equal values. -/
def diagonal : R →+* R × R := (RingHom.id R).prod (RingHom.id R)

/-- The normalization and the pinched point agree on the two endpoints. -/
theorem square :
    endpoints.comp (B (R := R)).val.toRingHom =
      diagonal.comp (bEval (R := R)).toRingHom := by
  apply RingHom.ext
  intro p
  apply Prod.ext
  · rfl
  · exact ((mem_B _).mp p.property).symm

/-- Linear interpolation extends every function on the two endpoints. -/
theorem endpoints_surjective : Function.Surjective (endpoints (R := R)) := by
  rintro ⟨a, b⟩
  refine ⟨C a + C (b - a) * X, ?_⟩
  apply Prod.ext <;> simp [endpoints]

/-- A function vanishes at both endpoints exactly when the conductor divides it. -/
theorem mem_ker_endpoints (p : R[X]) :
    p ∈ RingHom.ker (endpoints (R := R)) ↔ X * (X - 1) ∣ p := by
  constructor
  · intro hp
    have h0 : p.eval 0 = 0 := congrArg Prod.fst hp
    have h1 : p.eval 1 = 0 := congrArg Prod.snd hp
    let b : B (R := R) := ⟨p, (mem_B p).mpr (h0.trans h1.symm)⟩
    have hb : bEval b = 0 := h0
    simpa only [hb, map_zero, sub_zero] using conductor_dvd b
  · rintro ⟨q, rfl⟩
    change endpoints (X * (X - 1) * q) = 0
    apply Prod.ext <;> simp [endpoints]

/-- The kernel is the principal ideal of the two endpoints. -/
theorem ker_endpoints :
    RingHom.ker (endpoints (R := R)) = Ideal.span {X * (X - 1)} := by
  ext p
  rw [mem_ker_endpoints, Ideal.mem_span_singleton]

variable {S : Type*} [CommRing S]

/-- The universal ring map to the one-gon chart for a compatible pair. -/
def lift (f : S →+* R[X]) (g : S →+* R)
    (h : endpoints.comp f = diagonal.comp g) : S →+* B (R := R) :=
  f.codRestrict (B (R := R)).toSubring fun s ↦ by
    apply (mem_B _).mpr
    have hs := RingHom.congr_fun h s
    exact (congrArg Prod.fst hs).trans (congrArg Prod.snd hs).symm

theorem inclusion_lift (f : S →+* R[X]) (g : S →+* R)
    (h : endpoints.comp f = diagonal.comp g) :
    (B (R := R)).val.toRingHom.comp (lift f g h) = f := rfl

theorem evaluation_lift (f : S →+* R[X]) (g : S →+* R)
    (h : endpoints.comp f = diagonal.comp g) :
    (bEval (R := R)).toRingHom.comp (lift f g h) = g := by
  ext s
  exact congrArg Prod.fst (RingHom.congr_fun h s)

/-- Uniqueness of the map supplied by the ring pullback. -/
theorem lift_unique (f : S →+* R[X]) (g : S →+* R)
    (h : endpoints.comp f = diagonal.comp g)
    (k : S →+* B (R := R))
    (hk : (B (R := R)).val.toRingHom.comp k = f) :
    k = lift f g h := by
  apply RingHom.ext
  intro s
  exact Subtype.ext (RingHom.congr_fun hk s)

open CategoryTheory Limits

/-- The one-gon algebra is the categorical pullback of the two endpoint maps. -/
theorem isPullback :
    IsPullback (CommRingCat.ofHom (B (R := R)).val.toRingHom)
      (CommRingCat.ofHom (bEval (R := R)).toRingHom)
      (CommRingCat.ofHom endpoints) (CommRingCat.ofHom diagonal) := by
  have hw : CommRingCat.ofHom (B (R := R)).val.toRingHom ≫
      CommRingCat.ofHom endpoints =
      CommRingCat.ofHom (bEval (R := R)).toRingHom ≫
        CommRingCat.ofHom diagonal :=
    congrArg CommRingCat.ofHom square
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
    (fun s ↦ CommRingCat.ofHom
      (lift s.fst.hom s.snd.hom (congrArg CommRingCat.Hom.hom s.condition)))
    (fun s ↦ ?_) (fun s ↦ ?_) ?_)
  · apply CommRingCat.hom_ext
    exact inclusion_lift s.fst.hom s.snd.hom
      (congrArg CommRingCat.Hom.hom s.condition)
  · apply CommRingCat.hom_ext
    exact evaluation_lift s.fst.hom s.snd.hom
      (congrArg CommRingCat.Hom.hom s.condition)
  · intro s m hm _
    apply CommRingCat.hom_ext
    exact lift_unique s.fst.hom s.snd.hom
      (congrArg CommRingCat.Hom.hom s.condition) m.hom
      (congrArg CommRingCat.Hom.hom hm)

end FLT.Mazur.OneGonPinchingAlgebra
