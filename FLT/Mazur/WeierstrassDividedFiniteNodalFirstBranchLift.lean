/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteFlatBranchLift
public import FLT.Mazur.WeierstrassDividedNodalBranchCoefficients

/-!
# First branch outputs at arbitrary node depths above three input depths

The depth inequalities construct all required higher coefficient quotients.
The resulting actual finite-model output retains the complete tangent
contraction. Exact triple depth makes its entire nodal fiber smooth;
for larger depths the same output is the input to further resolution.
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
  {W : WeierstrassCurve R} {π : R} {start n k m : ℕ} (D : SplitNodeDepth W π m)
  (hdepth : 3 * (start + k) ≤ m)
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hk : k ≤ n)
  (a2 : R) (h2 : W.a₂ = π ^ (start + k) * a2)
variable (a c : Coordinate W (π ^ (start + k))
  (data ⟨k, Nat.lt_succ_of_le hk⟩).b3 (data ⟨k, Nat.lt_succ_of_le hk⟩).b4
  (data ⟨k, Nat.lt_succ_of_le hk⟩).b6 →ₐ[R] S)
local notation "d" => data ⟨k, Nat.lt_succ_of_le hk⟩
local notation "s" => π ^ (start + k)
local notation "B" => DividedTangentBranchRing W s (d).b3 (d).b4 (d).b6 a c
local notation "hπ" => D.uniformizer_ne_zero
local notation "b4'" => nodalBranchFourth D d hdepth
local notation "b6'" => nodalBranchConstant D d hdepth
local notation "h4'" => nodalBranchFourth_factor D d hdepth
local notation "h6'" => nodalBranchConstant_factor D d hdepth
local notation "res" => dividedTangentBranchRestriction W s (d).b3 (d).b4 (d).b6 a c
local notation "base" => finiteGlobalStructure hπ data k hk

/-- The actual first branch output with all higher coefficient quotients constructed. -/
def finiteNodalFirstBranchLift : Spec (.of B) ⟶ finiteGlobalModel hπ data k hk :=
  finiteFlatBranchLift hπ data k hk a2 b4' b6' (by simpa using h2)
    (by simpa using h4') (by simpa using h6') a c

/-- The original coefficient point is retained on the whole branch source. -/
@[reassoc] theorem finiteNodalFirstBranchLift_structure :
    finiteNodalFirstBranchLift D hdepth data hk a2 h2 a c ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) :=
  finiteFlatBranchLift_structure ..

/-- The output contracts to the exact original tangent sum. -/
@[reassoc] theorem finiteNodalFirstBranchLift_contraction :
    finiteNodalFirstBranchLift D hdepth data hk a2 h2 a c ≫ finiteGlobalContraction hπ data k hk =
      Spec.map (CommRingCat.ofHom (res).toRingHom) ≫
        dividedTangentToCurve W s (d).b3 (d).b4 (d).b6 a c
          (d).factor3 (d).factor4 (d).factor6 :=
  finiteFlatBranchLift_contraction ..

variable [IsNoetherianRing R]

/-- Every special-fiber branch point has smooth output at the original input depth. -/
theorem finiteNodalFirstBranchLift_smooth (hterminal : m = 3 * (start + k))
    (p : PrimeSpectrum B)
    (hp : algebraMap R B π ∈ p.asIdeal) :
    finiteNodalFirstBranchLift D hdepth data hk a2 h2 a c p ∈ (base).smoothLocus := by
  have hk0 : start + k ≠ 0 := by have h := D.depth_pos; omega
  have hs : algebraMap R B s ∈ p.asIdeal := by
    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    simp only [hr, pow_succ, map_mul]
    exact p.asIdeal.mul_mem_left _ hp
  have hlin := divided_linear_deep_mem D d (show start + k ≤ m + 1 by omega)
  have h3 : (d).b3 ∈ maximalIdeal R :=
    Ideal.pow_le_self (by omega : m + 1 - (start + k) ≠ 0) hlin.1
  rw [D.maximalIdeal_eq, Ideal.mem_span_singleton] at h3
  obtain ⟨b, hb⟩ := h3
  have h3' : algebraMap R B (d).b3 ∈ p.asIdeal := by
    have he := congrArg (algebraMap R B) hb
    rw [map_mul] at he
    exact he.symm ▸ p.asIdeal.mul_mem_right (algebraMap R B b) hp
  exact finiteFlatBranchLift_terminal_smooth hπ data k hk a2 b4' b6'
    (by simpa using h2) (by simpa using h4') (by simpa using h6') a c p hs h3'
    ((nodalBranchConstant_isUnit_iff D d hdepth).mpr hterminal)

end FLT.Mazur.WeierstrassDividedDepth
