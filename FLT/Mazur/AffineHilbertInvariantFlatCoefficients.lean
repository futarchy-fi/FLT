/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteBranchInvariants
public import FLT.Mazur.AffineBaseSectionAlgebra
public import FLT.Mazur.FlatAlgebraEqualizer

/-!
# Flat extension of the full original Hilbert invariant coefficients

Keep the original R-algebras on parameter and relation sections. Their full
invariant algebra commutes with flat scalar extension, including multiplication
and the original tensor inclusion. This is a coefficient theorem; identifying
tensors with geometric sections after arbitrary base change is separate work.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TensorProduct
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve Approximation SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
local notation "D" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
/-- The unchanged structural algebra on original source sections. -/
local instance sourceCoefficients : Algebra R Γ(A.left, ⊤) := affineBaseSectionAlgebra A.hom
/-- The unchanged structural algebra on full relation sections. -/
local instance relationCoefficients : Algebra R Γ((D).left, ⊤) :=
  affineBaseSectionAlgebra (D).hom

/-- The first complete endpoint, as an algebra map over the unchanged base ring. -/
def invariantFirstCoefficient : Γ(A.left, ⊤) →ₐ[R] Γ((D).left, ⊤) :=
  affineBaseSectionHom (D).hom A.hom (p).left (p).w

/-- The second complete endpoint retains its independent translation coordinate. -/
def invariantSecondCoefficient : Γ(A.left, ⊤) →ₐ[R] Γ((D).left, ⊤) :=
  affineBaseSectionHom (D).hom A.hom (q).left (q).w

local notation "α" => invariantFirstCoefficient f hL d V c k
local notation "β" => invariantSecondCoefficient f hL d V c k

/-- The full original invariant coefficients with their original R-algebra structure. -/
def invariantCoefficientAlgebra : Subalgebra R Γ(A.left, ⊤) := AlgHom.equalizer α β

/-- The algebra construction keeps literally the original invariant subring. -/
theorem invariantCoefficientAlgebra_toSubring :
    (invariantCoefficientAlgebra f hL d V c k).toSubring =
      compatibleFunctions (p).left (q).left := by
  ext s
  rfl

/-- On the constructed branch atlas these are exactly the simultaneous branch solutions. -/
theorem invariantCoefficientAlgebra_branches [Etale V.hom] [IsAffine A.left]
    [IsOpenImmersion k.left] :
    (invariantCoefficientAlgebra f hL d V c k).toSubring =
      RingHom.eqLocus (finiteBranchFirst f hL d V c k) (finiteBranchSecond f hL d V c k) := by
  rw [invariantCoefficientAlgebra_toSubring, finiteBranch_eqLocus]

variable (B : Type) [CommRing B] [Algebra R B] [Module.Flat R B]

/-- Actual flat scalar extension of the full invariant algebra, without an effectivity input. -/
def invariantCoefficientFlatEquiv :
    B ⊗[R] invariantCoefficientAlgebra f hL d V c k ≃ₐ[B]
      AlgHom.equalizer (FlatAlgebraEqualizer.tensorMap B α)
        (FlatAlgebraEqualizer.tensorMap B β) :=
  FlatAlgebraEqualizer.comparison α β B

/-- The isomorphism preserves the original pure tensor coefficients and new base scalars. -/
theorem invariantCoefficientFlatEquiv_tmul (b : B)
    (s : invariantCoefficientAlgebra f hL d V c k) :
    (invariantCoefficientFlatEquiv f hL d V c k B (b ⊗ₜ[R] s)).val = b ⊗ₜ[R] s.val := rfl

/-- Every solution of the two full tensor equations has a unique original invariant tensor. -/
theorem invariantCoefficientFlat_existsUnique (x : B ⊗[R] Γ(A.left, ⊤))
    (hx : FlatAlgebraEqualizer.tensorMap B α x = FlatAlgebraEqualizer.tensorMap B β x) :
    ∃! y : B ⊗[R] invariantCoefficientAlgebra f hL d V c k,
      FlatAlgebraEqualizer.tensorInclusion α β B y = x := by
  let z : AlgHom.equalizer (FlatAlgebraEqualizer.tensorMap B α)
      (FlatAlgebraEqualizer.tensorMap B β) := ⟨x, hx⟩
  let e := invariantCoefficientFlatEquiv f hL d V c k B
  refine ⟨e.symm z, congrArg Subtype.val (e.apply_symm_apply z), ?_⟩
  intro y hy
  apply e.injective
  exact (Subtype.ext hy).trans (e.apply_symm_apply z).symm

end FLT.Mazur.HilbertChart.AffineRestriction
