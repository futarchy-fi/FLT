/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteKernelEquations
public import FLT.Mazur.FiniteCoefficientKernelSubalgebra

/-!
# A Noetherian original-base coefficient model with the full candidate kernel

Construct the base algebra on the actual invariant subring, then adjoin the
finite kernel coefficients. This gives a Noetherian finite type algebra over
the original base, preserving every full candidate-kernel test. No effective
Picard quotient or flatness of the associated projection is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "B" => compatibleFunctions (Over.Hom.left p) (Over.Hom.left q)
local notation "l" => invariantKernelLeftCoefficients f hL d V c k
local notation "r" => invariantKernelRightCoefficients f hL d V c k

/-- The unchanged original coefficient-base map lands in the actual full invariant ring. -/
def invariantCoefficientBase : R →+* B :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫
    SchemeRelationInvariantSpectrum.invariantPullback (p).left (q).left A.hom
      (invariantAffine_base_condition f hL d V c k)).hom

/-- Retain the original base map as the algebra structure on full invariant coefficients. -/
local instance originalInvariantCoefficientAlgebra : Algebra R B :=
  (invariantCoefficientBase f hL d V c k).toAlgebra

/-- The finite type subalgebra consists of actual original invariant coefficients. -/
def finiteKernelCoefficientAlgebra : Subalgebra R B := by
  let _ := coefficientPairRing_isNoetherian f d V k
  exact FiniteCoefficientDifference.kernelSubalgebra R l r

local notation "C" => finiteKernelCoefficientAlgebra f hL d V c k

/-- The constructed coefficient model is finite type over the unchanged original base. -/
instance finiteKernelCoefficientAlgebra_finiteType : Algebra.FiniteType R C := by
  let _ := coefficientPairRing_isNoetherian f d V k
  exact FiniteCoefficientDifference.kernelSubalgebra_finiteType R l r

/-- Noetherianity is proved for the finite model, without asserting it for all invariants. -/
instance finiteKernelCoefficientAlgebra_isNoetherianRing : IsNoetherianRing C := by
  let _ : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  exact Algebra.FiniteType.isNoetherianRing R C

/-- The finite model preserves the literal original base coefficient map. -/
theorem finiteKernelCoefficientAlgebra_base :
    (C).val.toRingHom.comp (algebraMap R C) = invariantCoefficientBase f hL d V c k := rfl

/-- Restriction to the finite algebra leaves the entire equality ideal unchanged. -/
theorem finiteKernelCoefficientAlgebra_ideal :
    FiniteCoefficientDifference.differenceIdeal ((l).comp (C).val.toRingHom)
      ((r).comp (C).val.toRingHom) = FiniteCoefficientDifference.differenceIdeal l r := by
  let _ := coefficientPairRing_isNoetherian f d V k
  exact FiniteCoefficientDifference.kernelSubalgebra_differenceIdeal R l r

/-- Agreement on the finite algebra is precisely the full candidate kernel on every scheme test. -/
theorem finiteKernelCoefficientAlgebra_test {T : Over (Spec (.of R))} (a b : T ⟶ A) :
    a ≫ invariantAffineProjection f hL d V c k =
        b ≫ invariantAffineProjection f hL d V c k ↔
      ∀ s : C, a.left.appTop s.val.val = b.left.appTop s.val.val := by
  rw [finiteKernelCoefficients_test]
  constructor
  · intro h s
    have he := (finiteKernelCoefficients_test f hL d V c k a b).mpr h
    have hc := (SchemeRelationInvariantSpectrum.projection_test_eq_iff
      (p).left (q).left a.left b.left).mp (congrArg Over.Hom.left he)
    exact hc s.val
  · intro h s hs
    let _ := coefficientPairRing_isNoetherian f d V k
    exact h ⟨s, FiniteCoefficientDifference.coefficient_mem_kernelSubalgebra R l r s hs⟩

end FLT.Mazur.HilbertChart.AffineRestriction
