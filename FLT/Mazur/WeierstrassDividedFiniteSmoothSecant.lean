/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecantPrimeSmooth
public import FLT.Mazur.WeierstrassDividedResolvedOriginalOpen

/-!
# Smooth secant outputs in the same finite model over arbitrary sources

The inverse image of the original smooth locus carries a constructed
output in the actual finite model. A nodal prime with nonzero output
abscissa belongs to this open, without a field-valued-source restriction.
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
  (a c : WeierstrassDilatation.Coordinate W (π ^ (start + k))
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b3 (data ⟨k, Nat.lt_succ_of_le hk⟩).b4
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b6 →ₐ[R] S)
local notation "d" => data ⟨k, Nat.lt_succ_of_le hk⟩
local notation "s" => π ^ (start + k)
local notation "T" => DividedSecantRing W s (d).b3 (d).b4 (d).b6 a c
local notation "f" => dividedSecantToCurve W s (d).b3 (d).b4 (d).b6 a c
  (d).factor3 (d).factor4 (d).factor6
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "U" => (base).smoothLocus

/-- The actual open on which the original secant output is relatively smooth. -/
def finiteSmoothSecantOpen : (Spec (.of T)).Opens := f ⁻¹ᵁ integralSmoothOpen W

local notation "V" => finiteSmoothSecantOpen data k hk a c

/-- Construct the resolved smooth output by the proved original-smooth embedding. -/
def finiteSmoothSecantOutput : (V).toScheme ⟶ (U).toScheme :=
  (f ∣_ integralSmoothOpen W) ≫ finiteOriginalToResolved hπ data k hk

/-- This actual finite-model output contracts to the complete original secant formula. -/
@[reassoc] theorem finiteSmoothSecantOutput_contraction :
    finiteSmoothSecantOutput hπ data k hk a c ≫ (U).ι ≫
        finiteGlobalContraction hπ data k hk = (V).ι ≫ f := by
  rw [finiteSmoothSecantOutput, Category.assoc, finiteOriginalToResolved_inclusion_assoc,
    finiteGlobalSmoothEmbedding_contraction]
  exact morphismRestrict_ι _ _

/-- The output retains the coefficient morphism of the actual source open. -/
@[reassoc] theorem finiteSmoothSecantOutput_structure :
    finiteSmoothSecantOutput hπ data k hk a c ≫ (U).ι ≫ base =
      (V).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
  change _ ≫ (U).ι ≫ finiteGlobalContraction hπ data k hk ≫ integralCurveStructure W = _
  rw [finiteSmoothSecantOutput_contraction_assoc, dividedSecantToCurve_structure]

omit [IsDomain R] [IsBezout R] [IsNoetherianRing R] in
/-- Every nodal source prime with nonzero original output abscissa is covered by this output. -/
theorem finiteSmoothSecantOpen_mem (p : PrimeSpectrum T)
    (hs : algebraMap R T s ∈ p.asIdeal)
    (hx : dividedSecantX W s (d).b3 (d).b4 (d).b6 a c ∉ p.asIdeal) : p ∈ V :=
  dividedSecant_prime_smooth_of_x W s (d).b3 (d).b4 (d).b6 a c
    (d).factor3 (d).factor4 (d).factor6 p hs hx

/-- The entire constructed output lies in the relative smooth locus of the finite model. -/
theorem finiteSmoothSecantOutput_range :
    Set.range (finiteSmoothSecantOutput hπ data k hk a c ≫ (U).ι) ⊆ U := by
  rintro _ ⟨z, rfl⟩
  exact (finiteSmoothSecantOutput hπ data k hk a c z).property

end FLT.Mazur.WeierstrassDividedDepth
