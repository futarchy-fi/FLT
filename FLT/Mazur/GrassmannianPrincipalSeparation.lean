/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianLocalizedRelation
public import FLT.Mazur.GrassmannianAmbientPointCover

/-!
# Principal-local equality of original ambient quotients

Equality after a coefficient principal cover detects equality of the entire
original submodule of relations, without any reducedness or flatness hypothesis
on the original coefficient algebra.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A M κ : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Fintype κ] {d : ℕ}

omit [Fintype κ] in
/-- Actual Grassmannian functor points are separated on every coefficient principal cover. -/
theorem grassmannian_eq_of_localized_span (s : Set A) (hs : Ideal.span s = ⊤)
    (N P : Module.Grassmannian A (A ⊗[R] M) d)
    (h : ∀ r : s, Module.Grassmannian.map
      (IsScalarTower.toAlgHom R A (Localization.Away r.val)) N =
        Module.Grassmannian.map (IsScalarTower.toAlgHom R A (Localization.Away r.val)) P) :
    N = P := by
  apply Module.Grassmannian.ext
  apply Submodule.eq_of_isLocalized₀_span s hs
    (fun r ↦ Localization.Away r.val ⊗[R] M)
    (fun r ↦ AlgebraTensorModule.rTensor R M (Algebra.linearMap A (Localization.Away r.val)))
  intro r
  rw [← grassmannian_localized_relation, ← grassmannian_localized_relation, h r]

/-- The actual quotient chart cover's coefficients generate the unit ideal. -/
theorem ambientPointCover_span {ι : Type u} [Fintype ι] (b : Module.Basis ι R M)
    (N : Module.Grassmannian A (A ⊗[R] M) d) (hκ : Fintype.card κ = Fintype.card ι - d) :
    Ideal.span (Set.range (fun p : AmbientPointCoverIndex (κ := κ) N ↦ p.2.val)) = ⊤ := by
  by_contra h
  obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ h
  let _ := hp.isPrime
  obtain ⟨i, r, hr, hi⟩ := exists_functor_localized_chart b N hκ ⟨p, inferInstance⟩
  exact hr (hle (Ideal.subset_span ⟨⟨i, ⟨r, hi⟩⟩, rfl⟩))

/-- The actual principal cover of any quotient detects equality of any two original quotients. -/
theorem grassmannian_eq_of_pointCover {ι : Type u} [Fintype ι] (b : Module.Basis ι R M)
    (Q N P : Module.Grassmannian A (A ⊗[R] M) d)
    (hκ : Fintype.card κ = Fintype.card ι - d)
    (h : ∀ q : AmbientPointCoverIndex (κ := κ) Q, Module.Grassmannian.map
      (IsScalarTower.toAlgHom R A (Localization.Away q.2.val)) N =
        Module.Grassmannian.map (IsScalarTower.toAlgHom R A (Localization.Away q.2.val)) P) :
    N = P := by
  apply grassmannian_eq_of_localized_span _ (ambientPointCover_span b Q hκ)
  rintro ⟨r, q, rfl⟩
  exact h q

end FLT.Mazur.GrassmannianChart
