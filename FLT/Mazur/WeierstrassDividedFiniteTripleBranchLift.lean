/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteFlatBranchLift
public import FLT.Mazur.WeierstrassDividedTripleDepthCoefficients

/-!
# Smooth first branch outputs from exact triple node depth

At depth three times the input depth the constant quotient is a unit.
Every closed-fiber branch point has a smooth output in the depth-k model.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {start n k : ℕ} (D : SplitNodeDepth W π (3 * (start + k)))
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hk : k ≤ n)
  (a2 : R) (h2 : W.a₂ = π ^ (start + k) * a2)
variable (a c : Coordinate W (π ^ (start + k))
  (data ⟨k, Nat.lt_succ_of_le hk⟩).b3 (data ⟨k, Nat.lt_succ_of_le hk⟩).b4
  (data ⟨k, Nat.lt_succ_of_le hk⟩).b6 →ₐ[R] S)
local notation "d" => data ⟨k, Nat.lt_succ_of_le hk⟩
local notation "s" => π ^ (start + k)
local notation "B" => DividedTangentBranchRing W s (d).b3 (d).b4 (d).b6 a c
local notation "hπ" => D.uniformizer_ne_zero
local notation "b4'" => tripleDepthFourth D d
local notation "b6'" => tripleDepthConstant D d
local notation "h4'" => tripleDepthFourth_factor D d
local notation "h6'" => tripleDepthConstant_factor D d
local notation "res" => dividedTangentBranchRestriction W s (d).b3 (d).b4 (d).b6 a c
local notation "base" => finiteGlobalStructure hπ data k hk

/-- The actual first branch output with all higher coefficient quotients constructed. -/
def finiteTripleBranchLift : Spec (.of B) ⟶ finiteGlobalModel hπ data k hk :=
  finiteFlatBranchLift hπ data k hk a2 b4' b6' (by simpa using h2)
    (by simpa using h4') (by simpa using h6') a c

/-- The original coefficient point is retained on the whole branch source. -/
@[reassoc] theorem finiteTripleBranchLift_structure :
    finiteTripleBranchLift D data hk a2 h2 a c ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) :=
  finiteFlatBranchLift_structure ..

/-- The output contracts to the exact original tangent sum. -/
@[reassoc] theorem finiteTripleBranchLift_contraction :
    finiteTripleBranchLift D data hk a2 h2 a c ≫ finiteGlobalContraction hπ data k hk =
      Spec.map (CommRingCat.ofHom (res).toRingHom) ≫
        dividedTangentToCurve W s (d).b3 (d).b4 (d).b6 a c
          (d).factor3 (d).factor4 (d).factor6 :=
  finiteFlatBranchLift_contraction ..

variable [IsNoetherianRing R]

/-- Every special-fiber branch point has smooth output at the original input depth. -/
theorem finiteTripleBranchLift_smooth (p : PrimeSpectrum B)
    (hp : algebraMap R B π ∈ p.asIdeal) :
    finiteTripleBranchLift D data hk a2 h2 a c p ∈ (base).smoothLocus := by
  have hk0 : start + k ≠ 0 := by have h := D.depth_pos; omega
  have hs : algebraMap R B s ∈ p.asIdeal := by
    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    simp only [hr, pow_succ, map_mul]
    exact p.asIdeal.mul_mem_left _ hp
  have h3 := tripleDepth_third_mem D d
  rw [D.maximalIdeal_eq, Ideal.mem_span_singleton] at h3
  obtain ⟨b, hb⟩ := h3
  have h3' : algebraMap R B (d).b3 ∈ p.asIdeal := by
    have he := congrArg (algebraMap R B) hb
    rw [map_mul] at he
    exact he.symm ▸ p.asIdeal.mul_mem_right (algebraMap R B b) hp
  exact finiteFlatBranchLift_terminal_smooth hπ data k hk a2 b4' b6'
    (by simpa using h2) (by simpa using h4') (by simpa using h6') a c p hs h3'
    (tripleDepthConstant_isUnit D d)

end FLT.Mazur.WeierstrassDividedDepth
