/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.IntegralGroupLike
public import FLT.GroupScheme.RaynaudModelArithmetic
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-!
# Extension into split diagonalizable models

Generic maps into a model whose coordinate algebra is spanned by group-like
elements extend uniquely. There is no condition on the source's order or exponent.
The coordinate integrality follows from the finite convolution algebra of the
source, rather than from the order-three classification.

The spanning condition holds for group algebras, hence for split diagonalizable
targets. It is not asserted for arbitrary finite flat models.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan

/-- Generic images of integral group-like coordinates are integral in every source model. -/
theorem GenericGaloisHom.integral_of_isGroupLikeElem
    {X Y : FF ℤ_[3] ℚ_[3]} (f : GenericGaloisHom X Y)
    {y : Y.CoordinateRing} (hy : IsGroupLikeElem ℤ_[3] y) :
    ∃ x : X.CoordinateRing, f.toBialgHom (1 ⊗ₜ[ℤ_[3]] y) = 1 ⊗ₜ[ℤ_[3]] x := by
  let : Module.Free ℤ_[3] X.CoordinateRing := Module.free_of_flat_of_isLocalRing
  obtain ⟨x, hx⟩ := ((hy.baseChange (S := ℚ_[3])).map f.toBialgHom).exists_tmul_eq
  exact ⟨x, hx.symm⟩

/-- A target spanned by group-like coordinates makes every generic coordinate integral. -/
theorem GenericGaloisHom.integral_of_span_isGroupLikeElem
    {X Y : FF ℤ_[3] ℚ_[3]} (f : GenericGaloisHom X Y)
    (hY : Submodule.span ℤ_[3] {y : Y.CoordinateRing | IsGroupLikeElem ℤ_[3] y} = ⊤)
    (y : Y.CoordinateRing) :
    ∃ x : X.CoordinateRing, f.toBialgHom (1 ⊗ₜ[ℤ_[3]] y) = 1 ⊗ₜ[ℤ_[3]] x := by
  have hy : y ∈ Submodule.span ℤ_[3]
      {y : Y.CoordinateRing | IsGroupLikeElem ℤ_[3] y} := by rw [hY]; trivial
  induction hy using Submodule.span_induction with
  | mem y hy => exact f.integral_of_isGroupLikeElem hy
  | zero => exact ⟨0, by simp⟩
  | add a b ha hb ia ib =>
    obtain ⟨x, hx⟩ := ia
    obtain ⟨z, hz⟩ := ib
    exact ⟨x + z, by simp [TensorProduct.tmul_add, hx, hz]⟩
  | smul r y hy ih =>
    obtain ⟨x, hx⟩ := ih
    refine ⟨r • x, ?_⟩
    simp only [TensorProduct.tmul_smul, BialgHom.map_smul_of_tower, hx]

/-- Split diagonalizable targets have surjective first graph projections. -/
theorem GenericGaloisHom.graphFst_surjective_of_span_isGroupLikeElem
    {X Y : FF ℤ_[3] ℚ_[3]} (f : GenericGaloisHom X Y)
    (hY : Submodule.span ℤ_[3] {y : Y.CoordinateRing | IsGroupLikeElem ℤ_[3] y} = ⊤) :
    Function.Surjective f.graphFst :=
  f.graphFst_surjective_of_integral (f.integral_of_span_isGroupLikeElem hY)

/-- Generic maps into a model spanned by group-like coordinates extend uniquely. -/
theorem raynaud_extend_generic_morphism_of_span_isGroupLikeElem
    (X Y : FF ℤ_[3] ℚ_[3])
    (hY : Submodule.span ℤ_[3] {y : Y.CoordinateRing | IsGroupLikeElem ℤ_[3] y} = ⊤)
    (f : GenericGaloisHom X Y) : ∃! fO : ModelHom X Y, genericHom fO = f :=
  raynaud_extend_generic_morphism_of_graphFst_surjective X Y f
    (f.graphFst_surjective_of_span_isGroupLikeElem hY)

/-- A group-algebra presentation supplies the group-like spanning condition. -/
theorem FF.span_isGroupLikeElem_of_monoidAlgebra
    (Y : FF ℤ_[3] ℚ_[3]) {G : Type} [CommGroup G]
    (e : MonoidAlgebra ℤ_[3] G ≃ₐc[ℤ_[3]] Y.CoordinateRing) :
    Submodule.span ℤ_[3] {y : Y.CoordinateRing | IsGroupLikeElem ℤ_[3] y} = ⊤ := by
  apply top_unique
  intro y hy
  clear hy
  obtain ⟨a, rfl⟩ := e.surjective y
  induction a using MonoidAlgebra.induction_on with
  | of g =>
    exact Submodule.subset_span ((MonoidAlgebra.isGroupLikeElem_single_one g).map e)
  | add a b ha hb => simpa using Submodule.add_mem _ ha hb
  | smul r a ha => simpa using Submodule.smul_mem _ r ha

/-- Every generic morphism to a split diagonalizable target extends uniquely,
with no restriction on either the source or target exponent. -/
theorem raynaud_extend_generic_morphism_of_monoidAlgebra
    (X Y : FF ℤ_[3] ℚ_[3]) {G : Type} [CommGroup G]
    (e : MonoidAlgebra ℤ_[3] G ≃ₐc[ℤ_[3]] Y.CoordinateRing)
    (f : GenericGaloisHom X Y) : ∃! fO : ModelHom X Y, genericHom fO = f :=
  raynaud_extend_generic_morphism_of_span_isGroupLikeElem X Y
    (Y.span_isGroupLikeElem_of_monoidAlgebra e) f

end ThreeAdicPlan
