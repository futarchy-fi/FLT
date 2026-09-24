/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.Torsion
public import Mathlib.FieldTheory.Galois.Infinite

/-!
# Descent of fixed torsion points

Galois-fixed geometric points descend by descending their coordinates. Consequently an injective
map into geometric torsion whose image is fixed descends to rational points.

We use `torsionGaloisRepresentation`, the algebraic action underlying `galoisRep`. This avoids
requiring continuity, whose current construction uses the admitted finiteness of geometric
torsion. Neither ellipticity nor primality of the torsion exponent is needed for descent.
-/

@[expose] public section

noncomputable section

open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve

open WeierstrassCurve.Affine

/-- A point fixed by every automorphism of a Galois extension descends to the ground field. -/
theorem exists_point_of_galois_fixed {K L : Type*} [Field K] [Field L]
    [DecidableEq K] [DecidableEq L] [Algebra K L] [IsGalois K L]
    (E : WeierstrassCurve K) (P : (E⁄L).Point)
    (hP : ∀ g : L ≃ₐ[K] L, Point.map (W' := E) g.toAlgHom P = P) :
    ∃ Q : (E⁄K).Point, Point.baseChange K L Q = P := by
  cases P with
  | zero => exact ⟨0, rfl⟩
  | some x y h =>
    have hxy (g : L ≃ₐ[K] L) : g x = x ∧ g y = y :=
      Point.some.inj (hP g)
    obtain ⟨a, rfl⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed x).mpr
      (fun g ↦ (hxy g).1)
    obtain ⟨b, rfl⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed y).mpr
      (fun g ↦ (hxy g).2)
    exact ⟨.some a b ((E.toAffine.baseChange_nonsingular
      (Algebra.ofId K L).injective a b).mp h), rfl⟩

/-- An additive map with Galois-fixed image descends along injective point base change. -/
theorem exists_addHom_of_galois_fixed {K L A : Type*} [Field K] [Field L]
    [DecidableEq K] [DecidableEq L] [Algebra K L] [IsGalois K L] [AddZeroClass A]
    (E : WeierstrassCurve K) (f : A →+ (E⁄L).Point)
    (hf : ∀ (g : L ≃ₐ[K] L) a, Point.map (W' := E) g.toAlgHom (f a) = f a) :
    ∃ f₀ : A →+ (E⁄K).Point, ∀ a, Point.baseChange K L (f₀ a) = f a := by
  classical
  choose f₀ hf₀ using fun a ↦ E.exists_point_of_galois_fixed (f a) (fun g ↦ hf g a)
  have hinj := Point.map_injective (W' := E.toAffine) (Algebra.ofId K L)
  exact ⟨{
    toFun := f₀
    map_zero' := hinj (by simpa only [map_zero] using hf₀ 0)
    map_add' := fun a b ↦ hinj (by
      change Point.baseChange K L (f₀ (a + b)) =
        Point.baseChange K L (f₀ a + f₀ b)
      rw [map_add, hf₀, hf₀, hf₀, map_add]) }, hf₀⟩

/-- A fixed geometric torsion line gives an injection into rational points.

This generalizes the prime-torsion leaf to every exponent and every Weierstrass curve, using
its algebraic Galois action. The continuous representation has definitionally the same action,
but its continuity proof is unnecessary here. -/
theorem rational_torsion_of_fixed_line (E : WeierstrassCurve ℚ) (n : ℕ)
    (i : ZMod n →ₗ[ZMod n] (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion n)
    (hi : Function.Injective i)
    (hfixed : ∀ g x, E.torsionGaloisRepresentation n g (i x) = i x) :
    ∃ f : ZMod n →+ (E⁄ℚ).Point, Function.Injective f := by
  let j : ZMod n →+ (E⁄(AlgebraicClosure ℚ)).Point :=
    (Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point n).subtype.toAddMonoidHom.comp
      i.toAddMonoidHom
  obtain ⟨f, hf⟩ := E.exists_addHom_of_galois_fixed j (fun g x ↦
    congrArg Subtype.val (hfixed g x))
  refine ⟨f, fun a b hab ↦ hi (Subtype.ext ?_)⟩
  exact (hf a).symm.trans ((congrArg (Point.baseChange ℚ (AlgebraicClosure ℚ)) hab).trans
    (hf b))

end WeierstrassCurve
