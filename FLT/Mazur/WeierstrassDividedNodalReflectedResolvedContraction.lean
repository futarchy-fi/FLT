/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalReflectedNegative
public import FLT.Mazur.WeierstrassDividedNodalReflectedContraction

/-!
# Contraction of promoted reflected-depth outputs

Promotion through finite smooth models preserves the original secant
morphism on the complete constructed local source.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
attribute [local irreducible] rootShearCurve nodalSecondShear nodalSecondQuotient
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsNoetherianRing R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {k l m n : ℕ} (D : SplitNodeDepth W π m)
  (d : Data W π k) (e : Data W π l) (hkl : k ≤ l)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hd : m - k - l ≤ n)
  (hl : 2 * l ≤ m) (hm : m ≤ k + 2 * l)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "hπ" => D.uniformizer_ne_zero
local notation "z" => data ⟨m - k - l, Nat.lt_succ_of_le hd⟩
local notation "σ" => nodalSecondShear D (m - 2 * l)
local notation "V₀" => rootShearCurve W σ
local notation "sd" => (⟨d.b3, d.b4 - σ * d.b3, d.b6,
  (shearData d σ).factor3, (shearData d σ).factor4,
  (shearData d σ).factor6⟩ : Data V₀ π k)
local notation "se" => (⟨e.b3, e.b4 - σ * e.b3, e.b6,
  (shearData e σ).factor3, (shearData e σ).factor4,
  (shearData e σ).factor6⟩ : Data V₀ π l)
local notation "a'" => branchShearInput W (π ^ k) d.b3 d.b4 d.b6 σ a
local notation "c'" => branchShearInput W (π ^ l) e.b3 e.b4 e.b6 σ c
local notation "T" => SumDepthSourceRing sd se a' c'

local notation "o" => nodalReflectedSourceOutputAt d e a c D hkl hl hm z (Nat.zero_add _)
local notation "f" => nodalReflectedSourceLiftAt d e a c D hkl hl hm z (Nat.zero_add _)
local notation "base" => finiteGlobalStructure hπ data (m - k - l) hd
local notation "U" => (base).smoothLocus
local notation "inc" => finiteSecantDividedChart hπ data (m - k - l) hd

local notation "V" => nodalReflectedSmoothOpen D d e hkl data hd hl hm a c
local notation "res" => nodalReflectedSecantRestriction D d e hkl a c
local notation "c₀" => unequalDepthRight hπ d e hkl c

omit [IsBezout R] [IsNoetherianRing R] in
/-- The indexed finite-family lift contracts to the same restricted original secant. -/
@[reassoc] theorem nodalReflectedSourceLiftAt_contraction {r : ℕ} (w : Data W π r)
    (hr : r = m - k - l) :
    nodalReflectedSourceLiftAt d e a c D hkl hl hm w hr ≫ toCurve w =
      Spec.map (CommRingCat.ofHom (res).toRingHom) ≫
        dividedSecantToCurve W (π ^ k) d.b3 d.b4 d.b6 a c₀
          d.factor3 d.factor4 d.factor6 := by
  subst r
  exact nodalReflectedSourceLift_contraction D d e hkl hl hm w a c

variable (j : ℕ) (hj : j ≤ n) (hdj : m - k - l ≤ j)
local notation "final" => finiteGlobalStructure hπ data j hj
local notation "Uf" => (final).smoothLocus

/-- The resolved smooth output is the original addition after cubic contraction. -/
@[reassoc] theorem nodalReflectedResolvedOutput_contraction :
    nodalReflectedResolvedOutput D d e hkl data hd hl hm a c j hj hdj ≫
        (Uf).ι ≫ finiteGlobalContraction hπ data j hj =
      (V).ι ≫ Spec.map (CommRingCat.ofHom (res).toRingHom) ≫
        dividedSecantToCurve W (π ^ k) d.b3 d.b4 d.b6 a c₀
          d.factor3 d.factor4 d.factor6 := by
  rw [nodalReflectedResolvedOutput, Category.assoc, finiteGlobalSmoothTransition_contraction,
    morphismRestrict_ι_assoc, Category.assoc, finiteSecantDividedChart_contraction,
    nodalReflectedSourceLiftAt_contraction]
  rfl

local notation "na" => branchNegativeInput W (π ^ k) d.b3 d.b4 d.b6 a
local notation "nc" => branchNegativeInput W (π ^ l) e.b3 e.b4 e.b6 c
local notation "NV" => nodalReflectedSmoothOpen D d e hkl data hd hl hm na nc
local notation "nr" => nodalReflectedSecantRestriction D d e hkl na nc
local notation "nc₀" => unequalDepthRight hπ d e hkl nc

/-- Negating the promoted normalized output preserves its original cubic contraction. -/
@[reassoc] theorem nodalReflectedNegativeOutput_contraction :
    nodalReflectedResolvedOutput D d e hkl data hd hl hm na nc j hj hdj ≫
        finiteResolvedNegation hπ data j hj ≫ (Uf).ι ≫
          finiteGlobalContraction hπ data j hj =
      (NV).ι ≫ Spec.map (CommRingCat.ofHom (nr).toRingHom) ≫
        dividedSecantToCurve W (π ^ k) d.b3 d.b4 d.b6 na nc₀
          d.factor3 d.factor4 d.factor6 ≫ WeierstrassIntegralChart.integralCurveNegation W := by
  rw [finiteResolvedNegation_contraction, nodalReflectedResolvedOutput_contraction_assoc]

end FLT.Mazur.WeierstrassDividedDepth
