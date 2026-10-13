/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearInitialInfinityProjections
public import FLT.Mazur.WeierstrassResidueInfinitySlopeComparison
public import FLT.Mazur.WeierstrassCoefficientShearResidueExteriorAffine
public import FLT.Mazur.PrincipalOpenIntersectionModels

/-!
# The full original shifted infinity boundary has its original slope parameter

The two projections of the entire boundary supply the coefficient and cubic
comparisons. The extra original root shift remains in the localized polynomial.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open ProjectiveLine WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  (hstart : 0 < start) (hres : residue R π = 0)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "hk" => show 0 < start + (0 : Fin (n + 1)).val from by dsimp; omega
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
  (hs : algebraMap R (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
    (π ^ start) = 0)
  (h3 : algebraMap R (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
    (data ⟨0, Nat.zero_lt_succ n⟩).b3 = 0)
  (h4 : algebraMap R (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
    (data ⟨0, Nat.zero_lt_succ n⟩).b4 = 0)
local notation "hr" => residueTangentEquation_root W
local notation "L" => coefficientShearInitialLine hπ data Q r j hj hs h3 h4 hr
local notation "p" => coefficientShearGluedProjection hπ data Q r j hj
local notation "g" => coefficientShearGluedStructure hπ data Q r j hj
local notation "N" => originalResidueFiniteNormalization hπ data j hj d hk hres

variable (a : (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))ˣ)
  (ha : (a : AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) =
    (nodeTangentShear (W.map (residue R))).a₁)
local notation "α" => (rootShearCurve (W.map (algebraMap R Q)) r).a₁
local notation "P" => Localization.Away
  (slopePolynomial α * (Polynomial.X + Polynomial.C r))
local notation "p₀" => Spec.map (CommRingCat.ofHom (algebraMap (Polynomial Q) P))
local notation "b₀" => coefficientShearInitialInfinitySlope hπ data Q r j hj hs h3 h4 hr

/-- The actual infinity parameter equals the entire shifted punctured slope inclusion. -/
@[reassoc] theorem coefficientShearInitialInfinitySlope_parameter :
    b₀ ≫ residueInfinityTensorParameter d hk hres a ha = p₀ ≫ left Q := by
  have ha' : (a : Q) = α := ha
  let f : Spec (.of P) ⟶ Spec (.of (SlopeOpen (a : Q))) :=
    PrincipalLocalizationSquare.openInclusion (by
      rw [ha']
      exact PrimeSpectrum.basicOpen_mul_le_left _ _)
  have hf : f ≫ PrincipalOpenTransport.inclusion (slopePolynomial (a : Q)) = p₀ :=
    PrincipalLocalizationSquare.openInclusion_fac _
  have hf' : f ≫ PrincipalOpenTransport.inclusion (slopePolynomial (a : Q)) ≫ left Q =
      p₀ ≫ left Q := by rw [← Category.assoc, hf]
  rw [← hf']
  apply residueInfinityTensorParameter_slope d hk hres a ha f b₀
  · rw [← Category.assoc, ← Category.assoc, hf]
    simp only [Category.assoc]
    exact coefficientShearInitialInfinitySlope_structure hπ data Q r j hj hs h3 h4 hr
  · rw [← Category.assoc, ← Category.assoc, hf]
    simp only [Category.assoc]
    rw [coefficientShearInitialInfinitySlope_projection,
      coefficientShearResidueIncidenceLine_finiteProjection_assoc
        hπ data j hj hstart hres hs h3 h4,
      originalResidueFiniteNormalization_contraction]

end FLT.Mazur.WeierstrassDividedDepth
