/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalWiderReflectedResidue

/-!
# Normalized wider reflected output at an equal indexed depth

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
  (hkl : k ≤ l) (hm : k + 2 * l ≤ m) (htop : m ≤ 2 * (k + l))
  {r : ℕ} (z : Data W π r) (hr : r = m - k - l)
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
def nodalWiderReflectedSourceOutputAt : Coordinate W (π ^ r) z.b3 z.b4 z.b6 →ₐ[R] B := by
  subst r
  exact nodalWiderReflectedSourceOutput D d e hkl hm htop z a c

/-- The reindexed output as a morphism to the actual chart. -/
def nodalWiderReflectedSourceLiftAt : Spec (.of B) ⟶ chart z :=
  Spec.map (CommRingCat.ofHom
    (nodalWiderReflectedSourceOutputAt d e a c D hkl hm htop z hr).toRingHom)

/-- Reindexing preserves the coefficient point. -/
@[reassoc] theorem nodalWiderReflectedSourceLiftAt_structure :
    nodalWiderReflectedSourceLiftAt d e a c D hkl hm htop z hr ≫ Spec.map (CommRingCat.ofHom
      (algebraMap R (Coordinate W (π ^ r) z.b3 z.b4 z.b6))) =
        Spec.map (CommRingCat.ofHom (algebraMap R B)) :=
  WeierstrassIntegralChart.specAlgHom_structure _

/-- The actual reindexed output retains the same explicit residue smoothness criterion. -/
theorem nodalWiderReflectedSourceOutputAt_residue_vertical {K : Type u} [Field K] [Algebra R K]
    (ρ : B →ₐ[R] K) (hs : algebraMap R K (π ^ k) = 0)
    (ht : algebraMap R K (π ^ (l - k)) = 0)
    (hv : algebraMap R K (π ^ (2 * (k + l) - m)) = 0)
    (hz3 : algebraMap R K z.b3 = 0) :
    ρ (nodalWiderReflectedSourceOutputAt d e a c D hkl hm htop z hr
      (verticalDerivative W (π ^ r) z.b3 z.b4 z.b6)) ≠ 0 := by
  subst r
  exact nodalWiderReflectedSourceOutput_residue_vertical D d e hkl hm htop z a c
    ρ hs ht hv hz3

end FLT.Mazur.WeierstrassDividedDepth
