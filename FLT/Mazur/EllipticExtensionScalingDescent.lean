/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticScalingSmoothTorsion
public import FLT.Mazur.EllipticReductionBaseChange
public import FLT.Mazur.EllipticPointMapCoordinates

/-!
# Descent of the scaling obstruction through the actual field extension

A local extension preserves smooth reduction of the original point. The given
scaling over that same extension annihilates its prime torsion only when the
original point was zero. No replacement generator is chosen.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K L : Type*} [Field K] [Field L]

/-- Extending a projective point to a field extension reflects the identity. -/
theorem extensionProjectiveHom_eq_zero_iff (W : WeierstrassCurve K) (f : K →+* L)
    (V : WeierstrassCurve L) (he : W.map f = V) (P : W.toProjective.Point) :
    extensionProjectiveHom W f V he P = 0 ↔ P = 0 := by
  classical
  constructor
  · intro hz
    obtain ⟨Q, rfl⟩ := (Projective.Point.toAffineAddEquiv W.toProjective).symm.surjective P
    cases Q with
    | zero => exact map_zero _
    | some x y h =>
      have hn := extension_nonsingular W f V he h
      rw [Projective.Point.toAffineAddEquiv_symm_apply,
        extensionProjectiveHom_some W f V he h hn] at hz
      have hf := congrArg (Projective.Point.toAffineAddEquiv V.toProjective) hz
      change (Projective.Point.toAffineAddEquiv V.toProjective)
        ((Projective.Point.toAffineAddEquiv V.toProjective).symm (.some _ _ hn)) = _ at hf
      rw [AddEquiv.apply_symm_apply, map_zero] at hf
      cases hf
  · rintro rfl
    exact map_zero _

variable (A : ValuationSubring K) (B : ValuationSubring L)
  [IsDiscreteValuationRing B] [IsAdicComplete (maximalIdeal B) B]
  (W : WeierstrassCurve A) (f : K →+* L) (g : A →+* B) [IsLocalHom g]
  (hc : (algebraMap B L).comp g = f.comp (algebraMap A K))
  [((W.map g).map (algebraMap B L)).IsElliptic]

include f hc

/-- The original smooth prime-torsion point vanishes if its extension admits positive scaling. -/
theorem smooth_prime_torsion_eq_zero_of_extension_scaling
    (h3 : (W.map g).a₃ ∈ maximalIdeal B) (h4 : (W.map g).a₄ ∈ maximalIdeal B)
    (U : WeierstrassCurve B) (p : ℕ) [Fact p.Prime] (hp0 : (p : B) ≠ 0)
    (he : RaynaudParameters.order (p : B) < p - 1)
    (u : B) (hu : u ∈ maximalIdeal B) (C : VariableChange L)
    (hC : C • (W.map g).map (algebraMap B L) = U.map (algebraMap B L))
    (hCu : (C.u : L) = u) (hCr : C.r = 0) (hCs : C.s = 0) (hCt : C.t = 0)
    (P : (W.map (algebraMap A K)).toProjective.Point) (hP : p • P = 0)
    (hsm : SmoothReduction A W P) : P = 0 := by
  classical
  let E := integralProjectiveExtension A B W f g hc
  let T := Projective.Point.toAffineAddEquiv ((W.map g).map (algebraMap B L)).toProjective
  have hn : p • T (E P) = 0 := by rw [← map_nsmul, ← map_nsmul, hP, map_zero, map_zero]
  have hs : SmoothReduction B (W.map g) (T (E P)).toProjective := by
    have hs := (smoothReduction_integralProjectiveExtension A B W f g hc P).mpr hsm
    change SmoothReduction B (W.map g) (T.symm (T (E P)))
    rwa [AddEquiv.symm_apply_apply]
  have hz := smooth_prime_torsion_eq_zero_of_scaling B (W.map g) U h3 h4 p hp0 he
    u hu C hC hCu hCr hCs hCt (T (E P)) hn hs
  have hz' : E P = 0 := T.injective (hz.trans (map_zero T).symm)
  exact (extensionProjectiveHom_eq_zero_iff _ f _ _ P).mp hz'

end FLT.Mazur
