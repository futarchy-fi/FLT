/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecantPrimeSmooth
public import FLT.Mazur.WeierstrassDividedResolvedOriginalOpen

/-!
# Smooth secant outputs at an independently supplied finite-model depth

The inverse image of the original smooth locus carries a constructed
output in the actual finite model. A nodal prime with nonzero output
abscissa belongs to this open, without a field-valued-source restriction.
Input and target depths are independent.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation WeierstrassIntegralChart
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (k : ℕ) (hk : k ≤ n)
  {m : ℕ} (d : Data W π m)
  (a c : Coordinate W (π ^ m) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => π ^ m
local notation "T" => DividedSecantRing W s d.b3 d.b4 d.b6 a c
local notation "f" => dividedSecantToCurve W s d.b3 d.b4 d.b6 a c
  d.factor3 d.factor4 d.factor6
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "U" => (base).smoothLocus

/-- The actual open on which the original secant output is relatively smooth. -/
def finiteReindexedSmoothSecantOpen : (Spec (.of T)).Opens := f ⁻¹ᵁ integralSmoothOpen W

local notation "V" => finiteReindexedSmoothSecantOpen d a c

/-- Construct the resolved smooth output by the proved original-smooth embedding. -/
def finiteReindexedSmoothSecantOutput : (V).toScheme ⟶ (U).toScheme :=
  (f ∣_ integralSmoothOpen W) ≫ finiteOriginalToResolved hπ data k hk

/-- This actual finite-model output contracts to the complete original secant formula. -/
@[reassoc] theorem finiteReindexedSmoothSecantOutput_contraction :
    finiteReindexedSmoothSecantOutput hπ data k hk d a c ≫ (U).ι ≫
        finiteGlobalContraction hπ data k hk = (V).ι ≫ f := by
  rw [finiteReindexedSmoothSecantOutput, Category.assoc, finiteOriginalToResolved_inclusion_assoc,
    finiteGlobalSmoothEmbedding_contraction]
  exact morphismRestrict_ι _ _

/-- The output retains the coefficient morphism of the actual source open. -/
@[reassoc] theorem finiteReindexedSmoothSecantOutput_structure :
    finiteReindexedSmoothSecantOutput hπ data k hk d a c ≫ (U).ι ≫ base =
      (V).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
  change _ ≫ (U).ι ≫ finiteGlobalContraction hπ data k hk ≫ integralCurveStructure W = _
  rw [finiteReindexedSmoothSecantOutput_contraction_assoc, dividedSecantToCurve_structure]

omit [IsDomain R] [IsBezout R] [IsNoetherianRing R] in
/-- Every nodal source prime with nonzero original output abscissa is covered by this output. -/
theorem finiteReindexedSmoothSecantOpen_mem (p : PrimeSpectrum T)
    (hs : algebraMap R T s ∈ p.asIdeal)
    (hx : dividedSecantX W s d.b3 d.b4 d.b6 a c ∉ p.asIdeal) : p ∈ V :=
  dividedSecant_prime_smooth_of_x W s d.b3 d.b4 d.b6 a c
    d.factor3 d.factor4 d.factor6 p hs hx

/-- The entire constructed output lies in the relative smooth locus of the finite model. -/
theorem finiteReindexedSmoothSecantOutput_range :
    Set.range (finiteReindexedSmoothSecantOutput hπ data k hk d a c ≫ (U).ι) ⊆ U := by
  rintro _ ⟨z, rfl⟩
  exact (finiteReindexedSmoothSecantOutput hπ data k hk d a c z).property

end FLT.Mazur.WeierstrassDividedDepth
