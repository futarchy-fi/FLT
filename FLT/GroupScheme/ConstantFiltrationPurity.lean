/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.FilteredPointPurity
public import FLT.GaloisRepresentation.HardlyRamified.TrivialPrimeFiltrationExtension
public import FLT.GroupScheme.ConstantFiniteFlat
public import FLT.GroupScheme.FiniteFlatFiltration
public import FLT.GroupScheme.PointFieldEvaluation

/-!
# Purity of integral constant-three filtrations

An integral filtration by the constant group of order three induces a filtration
of geometric points and an étale model. The resulting rational Galois action is
trivial. This proves the constant-filtration case of R11, without needing the
additional category-D restrictions.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

/-- A model with the coordinate algebra of the zero group has only one point. -/
theorem HasFiniteFlatModel.subsingleton_of_coordinateEquiv
    {R : Type} [CommRing R] [Algebra R ℚ] {W : FiniteContinuousGaloisModule}
    (M : HasFiniteFlatModel R W) (e : M.CoordinateRing ≃ₐ[R] R) : Subsingleton W := by
  constructor
  intro x y
  apply M.pointFieldPoint_injective
  apply AlgHom.ext
  intro a
  have h : (M.pointFieldPoint x).comp e.symm.toAlgHom =
      (M.pointFieldPoint y).comp e.symm.toAlgHom := Subsingleton.elim _ _
  simpa using AlgHom.congr_fun h (e a)

/-- The constant group of order three is étale over `ℤ[1/2]`. -/
theorem constantThree_etale : Algebra.Etale ZInvTwo constantThree.model.CoordinateRing :=
  (constantEtaleModel (ZMod 3)).etale

/-- The points of the constant group of order three are killed by three. -/
theorem constantThree_nsmul (a : constantThree.points) : (3 : ℕ) • a = 0 := by
  revert a
  change ∀ a : ZMod 3, (3 : ℕ) • a = 0
  intro a
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

/-- The constant group of order three has trivial point action. -/
theorem constantThree_smul (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (a : constantThree.points) : σ • a = a := rfl

/-- An integral constant-three filtration gives a trivial three-torsion filtration
of the actual geometric point module. -/
theorem HasFiltration.trivialThreePoints {H : FiniteFlatObject ZInvTwo}
    (hF : HasFiltration H constantThree) :
    Nonempty (TrivialPrimeFiltration 3
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) H.points) := by
  generalize hQ : constantThree = Q at hF
  induction hF with
  | zero e =>
    let := HasFiniteFlatModel.subsingleton_of_coordinateEquiv _ e
    exact ⟨TrivialPrimeFiltration.ofTrivial (fun _ ↦ Subsingleton.elim _ _)
      (fun _ _ ↦ Subsingleton.elim _ _)⟩
  | single Q =>
    subst Q
    exact ⟨TrivialPrimeFiltration.ofTrivial constantThree_nsmul constantThree_smul⟩
  | @extension A H Q E hA ih =>
    subst Q
    obtain ⟨F⟩ := ih rfl
    exact ⟨F.extension (FiniteFlatObject.pointMap E.inclusion)
      (FiniteFlatObject.pointMap E.quotient)
      E.pointsExact constantThree_nsmul constantThree_smul⟩

/-- Every finite-flat group over `ℤ[1/2]` filtered by constant groups of order
three has pointwise trivial rational Galois action. -/
theorem pure_one_of_constantThree_filtration (H : FiniteFlatObject ZInvTwo)
    (hf : HasFiltration H constantThree) :
    Pure H.points (1 : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℤ) := by
  obtain ⟨F⟩ := hf.trivialThreePoints
  let M : FiniteEtaleModel ZInvTwo H.points :=
    { toHasFiniteFlatModel := H.model, etale := hf.etale constantThree_etale }
  exact H.points.pure_one_of_etale_trivialThreeFiltration F M

/-- The constant-filtration case of category-D purity, for the full geometric
point action. The category-D assumption is unnecessary for this stronger result. -/
@[nolint unusedArguments]
theorem D_etale_three_constant (H : FiniteFlatObject ZInvTwo) (_hD : InCategoryD H)
    (hf : HasFiltration H constantThree) :
    Pure H.points (1 : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℤ) :=
  pure_one_of_constantThree_filtration H hf

end ThreeAdicPlan
