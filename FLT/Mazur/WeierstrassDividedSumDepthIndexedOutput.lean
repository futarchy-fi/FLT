/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSumDepthSourceOutput
public import FLT.Mazur.WeierstrassDividedOwnSumDepthResidue

/-!
# Sum-depth output at an equal indexed depth

Finite model families index depth as zero plus a natural number. Transport
the actual source output along numerical equality, preserving its structure
and the residue criterion without unfolding any localization.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {W : WeierstrassCurve R} {π : R} {k l : ℕ} (d : Data W π k) (e : Data W π l)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
  [IsDomain R] [Module.Flat R S] (hπ : π ≠ 0) (hkl : k ≤ l)
  (dd : Data W π (k + k)) (ee : Data W π (l + l)) {r : ℕ} (z : Data W π r)
  (hr : r = k + l) (h2 : W.a₂ = 0)
local notation "B" => SumDepthSourceRing d e a c
local notation "j" => IsScalarTower.toAlgHom R S B

/-- Reindex the constructed output to an equal depth in a finite family. -/
def sumDepthSourceOutputAt : Coordinate W (π ^ r) z.b3 z.b4 z.b6 →ₐ[R] B := by
  subst r
  exact sumDepthSourceOutput d e a c hπ hkl dd ee z h2

/-- The reindexed output as a morphism to the actual chart. -/
def sumDepthSourceLiftAt : Spec (.of B) ⟶ chart z :=
  Spec.map (CommRingCat.ofHom
    (sumDepthSourceOutputAt d e a c hπ hkl dd ee z hr h2).toRingHom)

/-- Reindexing preserves the coefficient point. -/
@[reassoc] theorem sumDepthSourceLiftAt_structure :
    sumDepthSourceLiftAt d e a c hπ hkl dd ee z hr h2 ≫ Spec.map (CommRingCat.ofHom
      (algebraMap R (Coordinate W (π ^ r) z.b3 z.b4 z.b6))) =
        Spec.map (CommRingCat.ofHom (algebraMap R B)) :=
  WeierstrassIntegralChart.specAlgHom_structure _

/-- The actual reindexed output retains the same explicit residue smoothness criterion. -/
theorem sumDepthSourceOutputAt_residue_vertical {K : Type u} [Field K] [Algebra R K]
    (ρ : B →ₐ[R] K) (hs : algebraMap R K (π ^ k) = 0)
    (ht : algebraMap R K (π ^ (l - k)) = 0) (h3 : algebraMap R K d.b3 = 0)
    (h4 : algebraMap R K dd.b4 = 0) (hz3 : algebraMap R K z.b3 = 0)
    (hz6 : algebraMap R K z.b6 = 0) (ha : algebraMap R K W.a₁ ≠ 0) :
    ρ (sumDepthSourceOutputAt d e a c hπ hkl dd ee z hr h2
      (verticalDerivative W (π ^ r) z.b3 z.b4 z.b6)) ≠ 0 := by
  subst r
  exact ownSumDepthOutput_residue_vertical hπ d e hkl dd ee z h2
    ((j).comp a) ((j).comp c) (sumDepthSource_leftUnit d e a c)
    (sumDepthSource_rightUnit d e a c) (sumDepthSource_abscissaUnit d e a c)
    (sumDepthSourceInverse d e a c hπ hkl) (sumDepthSourceSlope d e a c hπ hkl)
    (sumDepthSourceInverse_relation d e a c hπ hkl)
    (sumDepthSourceSlope_relation d e a c hπ hkl) ρ hs ht h3 h4 hz3 hz6 ha

end FLT.Mazur.WeierstrassDividedDepth
