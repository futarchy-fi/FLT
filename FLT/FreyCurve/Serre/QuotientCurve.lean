/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.FixedLineDescent

/-!
# Point-level consequences of a quotient isogeny

These lemmas isolate the algebra and descent needed for the trivial-quotient branch of
Serre's argument. Constructing the quotient elliptic curve and its geometric point map
remains a separate geometric input.
-/

@[expose] public section

namespace AddMonoidHom

/-- A map with the same kernel as a surjection induces an injection from its target. -/
theorem exists_injective_factor_of_ker_eq {A B C : Type*}
    [AddGroup A] [AddGroup B] [AddGroup C]
    (q : A →+ B) (hq : Function.Surjective q) (f : A →+ C)
    (hker : q.ker = f.ker) :
    ∃ j : B →+ C, Function.Injective j ∧ ∀ a, j (q a) = f a := by
  let j := q.liftOfSurjective hq ⟨f, hker.le⟩
  have hj (a : A) : j (q a) = f a :=
    q.liftOfRightInverse_comp_apply _ _ _ a
  refine ⟨j, (injective_iff_map_eq_zero j).mpr ?_, hj⟩
  intro b hb
  obtain ⟨a, rfl⟩ := hq b
  have ha : a ∈ f.ker := (hj a).symm.trans hb
  exact show a ∈ q.ker from hker.symm ▸ ha

end AddMonoidHom

open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve

/-- An equivariant map on geometric torsion with kernel equal to that of a trivial
quotient embeds that quotient into rational points of the target curve. No existence
of a quotient curve or isogeny is asserted here. -/
theorem rational_torsion_of_trivial_quotient_image
    (E E' : WeierstrassCurve ℚ) (n : ℕ)
    (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion n →ₗ[ZMod n] ZMod n)
    (hq : Function.Surjective q)
    (hfixed : ∀ g v, q (E.torsionGaloisRepresentation n g v) = q v)
    (ψ : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion n →+
      (E'⁄(AlgebraicClosure ℚ)).Point)
    (hψ : ∀ g v, ψ (E.torsionGaloisRepresentation n g v) =
      Affine.Point.map (W' := E') g.toAlgHom (ψ v))
    (hker : q.toAddMonoidHom.ker = ψ.ker) :
    ∃ f : ZMod n →+ (E'⁄ℚ).Point, Function.Injective f ∧
      ∀ v, Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) (f (q v)) = ψ v := by
  obtain ⟨j, hj, hjq⟩ := q.toAddMonoidHom.exists_injective_factor_of_ker_eq hq ψ hker
  change ∀ v, j (q v) = ψ v at hjq
  have hjfixed (g : Field.absoluteGaloisGroup ℚ) (x : ZMod n) :
      Affine.Point.map (W' := E') g.toAlgHom (j x) = j x := by
    obtain ⟨v, rfl⟩ := hq x
    rw [hjq, ← hψ, ← hjq, hfixed, hjq]
  obtain ⟨f, hf⟩ := E'.exists_addHom_of_galois_fixed j hjfixed
  refine ⟨f, fun a b hab ↦ hj ?_, fun v ↦ (hf (q v)).trans (hjq v)⟩
  exact (hf a).symm.trans
    ((congrArg (Affine.Point.baseChange ℚ (AlgebraicClosure ℚ)) hab).trans (hf b))

end WeierstrassCurve
