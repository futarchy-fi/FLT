/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTerminalBranch
public import FLT.Mazur.WeierstrassSuccessiveArithmeticBoundaryCoverage

/-!
# The complete terminal arithmetic horizontal open is covered by both Laurent branches

Coverage is transported through the original depth transition. The image
union is exactly the original divided D(x), with no residue reduction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R]
  {W : WeierstrassCurve R} {π : R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (m : ℕ)
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

variable (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 d) (Data.b4 d) (Data.b6 d) 0
local notation "a" => depthOverlapEquiv W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d)

variable (ha : IsUnit W.a₁) (hs : π ∣ π ^ (start + j)) (h2 : π ∣ W.a₂)
  (h3 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3)
  (h4 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4)
  (h6 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6)
local notation "b" => arithmeticBranchLeftBoundary π m W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6
local notation "A" => PrincipalOpenTensor.transitionIso Q x t a
/-- Both original terminal Laurent branches cover the entire divided tensor localization. -/
theorem terminalArithmeticBoundaries_cover
    (p : Spec (.of (Localization.Away ((1 : Q) ⊗ₜ[R] x)))) :
    ∃ (opposite : Bool), ∃ z, (b opposite ≫ (A).hom) z = p := by
  obtain ⟨opposite, z, hz⟩ := arithmeticLeftBoundaries_cover π m W
    (π ^ (start + j)) (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6 ((A).inv p)
  refine ⟨opposite, z, ?_⟩
  change (A).hom (b opposite z) = p
  rw [hz]
  exact congrArg (fun f ↦ f p) (A).inv_hom_id

/-- The terminal branch images are precisely the whole original divided horizontal open. -/
theorem terminalArithmeticBoundaries_image
    (p : Spec (.of (WeierstrassDilatation.ScalarExtension W (π ^ (start + j + 1))
      (Data.b3 d) (Data.b4 d) (Data.b6 d) Q))) :
    (∃ (opposite : Bool), ∃ z,
      terminalArithmeticBranchBoundary data m j hj ha hs h2 h3 h4 h6 opposite z = p) ↔
        ∃ y, PrincipalOpenTensor.inclusion Q x y = p := by
  constructor
  · rintro ⟨opposite, z, hz⟩
    exact ⟨(b opposite ≫ (A).hom) z, hz⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨opposite, z, hz⟩ :=
      terminalArithmeticBoundaries_cover data m j hj ha hs h2 h3 h4 h6 y
    refine ⟨opposite, z, ?_⟩
    change PrincipalOpenTensor.inclusion Q x ((b opposite ≫ (A).hom) z) = _
    rw [hz]

end FLT.Mazur.WeierstrassDividedDepth
