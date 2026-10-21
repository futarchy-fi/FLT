/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSumDepthSmoothOutput
public import FLT.Mazur.WeierstrassDividedSumDepthContraction

/-!
# Contraction of promoted sum-depth outputs

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
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k l n : ℕ}
  (d : Data W π k) (e : Data W π l) (hkl : k ≤ l)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hd : k + l ≤ n)
  (dd : Data W π (k + k)) (ee : Data W π (l + l)) (h2 : W.a₂ = 0)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "z" => data ⟨k + l, Nat.lt_succ_of_le hd⟩
local notation "T" => SumDepthSourceRing d e a c
local notation "o" => sumDepthSourceOutputAt d e a c hπ hkl dd ee z (Nat.zero_add _) h2
local notation "f" => sumDepthSourceLiftAt d e a c hπ hkl dd ee z (Nat.zero_add _) h2
local notation "base" => finiteGlobalStructure hπ data (k + l) hd
local notation "U" => (base).smoothLocus
local notation "inc" => finiteSecantDividedChart hπ data (k + l) hd

local notation "V" => sumDepthSmoothOpen hπ d e hkl data hd dd ee h2 a c
local notation "res" => sumDepthSourceRestriction d e a c hπ hkl
local notation "c₀" => unequalDepthRight hπ d e hkl c

omit [IsBezout R] [IsNoetherianRing R] in
/-- The indexed finite-family lift contracts to the same restricted original secant. -/
@[reassoc] theorem sumDepthSourceLiftAt_contraction {r : ℕ} (w : Data W π r)
    (hr : r = k + l) :
    sumDepthSourceLiftAt d e a c hπ hkl dd ee w hr h2 ≫ toCurve w =
      Spec.map (CommRingCat.ofHom (res).toRingHom) ≫
        dividedSecantToCurve W (π ^ k) d.b3 d.b4 d.b6 a c₀
          d.factor3 d.factor4 d.factor6 := by
  subst r
  exact sumDepthSourceLift_contraction d e a c hπ hkl dd ee w h2

variable (j : ℕ) (hj : j ≤ n) (hdj : k + l ≤ j)
local notation "final" => finiteGlobalStructure hπ data j hj
local notation "Uf" => (final).smoothLocus

/-- The resolved smooth output is the original addition after cubic contraction. -/
@[reassoc] theorem sumDepthResolvedOutput_contraction :
    sumDepthResolvedOutput hπ d e hkl data hd dd ee h2 a c j hj hdj ≫
        (Uf).ι ≫ finiteGlobalContraction hπ data j hj =
      (V).ι ≫ Spec.map (CommRingCat.ofHom (res).toRingHom) ≫
        dividedSecantToCurve W (π ^ k) d.b3 d.b4 d.b6 a c₀
          d.factor3 d.factor4 d.factor6 := by
  rw [sumDepthResolvedOutput, Category.assoc, finiteGlobalSmoothTransition_contraction,
    morphismRestrict_ι_assoc, Category.assoc, finiteSecantDividedChart_contraction,
    sumDepthSourceLiftAt_contraction]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
