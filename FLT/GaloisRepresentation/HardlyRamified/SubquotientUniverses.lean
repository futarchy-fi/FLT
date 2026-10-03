/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlatSubobjectUniverses
public import FLT.GroupScheme.FiniteFlatQuotientUniverses

/-! # Integral subquotient models for point modules in arbitrary universes -/

@[expose] public noncomputable section
namespace ThreeAdicPlan

/-- An equivariant quotient of an equivariant image in a finite-flat module
is finite flat. The kernel inclusion expresses that the second map factors
through the image of the first. -/
theorem finiteFlat_of_subquotient_universes
    {R F L : Type} {X Y Z : Type*} [CommRing R] [Field F] [Field L]
    [Algebra R F] [Algebra F L] [IsDedekindDomain R] [IsFractionRing R F]
    [IsGalois F L] [IsSepClosed L]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [DistribMulAction (L ≃ₐ[F] L) X] [DistribMulAction (L ≃ₐ[F] L) Y]
    [DistribMulAction (L ≃ₐ[F] L) Z]
    (hX : GaloisModule.IsFiniteFlat R F L X)
    (f : Y →+[L ≃ₐ[F] L] X) (q : Y →+[L ≃ₐ[F] L] Z)
    (hq : Function.Surjective q)
    (hker : f.toAddMonoidHom.ker ≤ q.toAddMonoidHom.ker) :
    GaloisModule.IsFiniteFlat R F L Z := by
  let S := f.toAddMonoidHom.range
  let _ : SMul (L ≃ₐ[F] L) S := ⟨fun g x ↦
    ⟨g • x.val, by
      obtain ⟨y, hy⟩ := x.property
      exact ⟨g • y, (map_smul f g y).trans (congrArg (g • ·) hy)⟩⟩⟩
  let _ : DistribMulAction (L ≃ₐ[F] L) S :=
    Function.Injective.distribMulAction S.subtype Subtype.val_injective (fun _ _ ↦ rfl)
  let i : S →+[L ≃ₐ[F] L] X :=
    { S.subtype with map_smul' := fun _ _ ↦ rfl }
  have hS := hX.subobject_universes R F L X i Subtype.val_injective
  let f' : Y →+ S := f.toAddMonoidHom.rangeRestrict
  have hf' : Function.Surjective f' := f.toAddMonoidHom.rangeRestrict_surjective
  have hk : f'.ker ≤ q.toAddMonoidHom.ker := by
    intro y hy
    apply hker
    exact congrArg Subtype.val hy
  let q' : S →+ Z := f'.liftOfSurjective hf' ⟨q.toAddMonoidHom, hk⟩
  have hq' (y : Y) : q' (f' y) = q y := by simp [q']
  let t : S →+[L ≃ₐ[F] L] Z :=
    { q' with
      map_smul' := by
        intro g x
        obtain ⟨y, rfl⟩ := hf' x
        have he : g • f' y = f' (g • y) := Subtype.ext (map_smul f g y).symm
        change q' (g • f' y) = g • q' (f' y)
        rw [he, hq', hq', map_smul] }
  apply hS.quotient_universes R F L S t
  intro z
  obtain ⟨y, rfl⟩ := hq z
  exact ⟨f' y, hq' y⟩


end ThreeAdicPlan
