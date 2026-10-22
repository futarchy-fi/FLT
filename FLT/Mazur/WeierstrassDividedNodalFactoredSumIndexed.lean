/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalFactoredSumResidue

/-!
# Normalized sum-depth output at an equal indexed depth

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
attribute [local irreducible] rootShearCurve nodalSecondShear nodalSecondQuotient
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {W : WeierstrassCurve R} {π : R} {k l m : ℕ} (d : Data W π k) (e : Data W π l)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
  [IsDomain R] [IsLocalRing R] [Module.Flat R S] (D : SplitNodeDepth W π m)
  (hkl : k ≤ l) (hm : k + 2 * l ≤ m)
  {r : ℕ} (z : Data W π r) (hr : r = k + l)
local notation "σ" => nodalSecondShear D k
local notation "V" => rootShearCurve W σ
local notation "sd" => (⟨d.b3, d.b4 - σ * d.b3, d.b6,
  (shearData d σ).factor3, (shearData d σ).factor4,
  (shearData d σ).factor6⟩ : Data V π k)
local notation "se" => (⟨e.b3, e.b4 - σ * e.b3, e.b6,
  (shearData e σ).factor3, (shearData e σ).factor4,
  (shearData e σ).factor6⟩ : Data V π l)
local notation "a'" => branchShearInput W (π ^ k) d.b3 d.b4 d.b6 σ a
local notation "c'" => branchShearInput W (π ^ l) e.b3 e.b4 e.b6 σ c
local notation "B" => SumDepthSourceRing sd se a' c'

/-- Reindex the constructed output to an equal depth in a finite family. -/
def nodalFactoredSumSourceOutputAt : Coordinate W (π ^ r) z.b3 z.b4 z.b6 →ₐ[R] B := by
  subst r
  exact nodalFactoredSumSourceOutput D d e hkl hm z a c

/-- The reindexed output as a morphism to the actual chart. -/
def nodalFactoredSumSourceLiftAt : Spec (.of B) ⟶ chart z :=
  Spec.map (CommRingCat.ofHom
    (nodalFactoredSumSourceOutputAt d e a c D hkl hm z hr).toRingHom)

/-- Reindexing preserves the coefficient point. -/
@[reassoc] theorem nodalFactoredSumSourceLiftAt_structure :
    nodalFactoredSumSourceLiftAt d e a c D hkl hm z hr ≫ Spec.map (CommRingCat.ofHom
      (algebraMap R (Coordinate W (π ^ r) z.b3 z.b4 z.b6))) =
        Spec.map (CommRingCat.ofHom (algebraMap R B)) :=
  WeierstrassIntegralChart.specAlgHom_structure _

/-- The actual reindexed output retains the same explicit residue smoothness criterion. -/
theorem nodalFactoredSumSourceOutputAt_residue_vertical {K : Type u} [Field K] [Algebra R K]
    (hk : 0 < k) (hlt : k < l) (hdeep : 2 * (k + l) < m)
    (ρ : B →ₐ[R] K) (hπ0 : algebraMap R K π = 0) :
    ρ (nodalFactoredSumSourceOutputAt d e a c D hkl hm z hr
      (verticalDerivative W (π ^ r) z.b3 z.b4 z.b6)) ≠ 0 := by
  subst r
  exact nodalFactoredSumSourceOutput_residue_vertical D d e hkl hm z a c
    hk hlt hdeep ρ hπ0

end FLT.Mazur.WeierstrassDividedDepth
