/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalExterior
public import FLT.Mazur.WeierstrassSuccessiveShearScaleOneConicBoundary
public import FLT.Mazur.PrincipalOpenVanishingIntersection
public import FLT.Mazur.WeierstrassDividedOlderGlobalInfinityIntersection

/-!
# The original scale-one conic misses the full exterior and infinity

The actual tensor conic kills the entire horizontal boundary function.
The full empty intersection persists through every retained global embedding.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (j : ℕ) (hj : j + 1 ≤ n) (m : ℕ) (hm : j + 1 + m ≤ n)
local notation "d" => data ⟨j + 1, Nat.lt_succ_of_le hj⟩
variable (hs : algebraMap R S (π ^ (start + j)) = 1) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "C" => tensorShearScaleOneConicImmersion W (π ^ (start + j)) π
  (d).b3 (d).b4 (d).b6 S r hs hp h3 h4 hr
local notation "f" => tensorShearScaleOneConicMap W (π ^ (start + j)) π
  (d).b3 (d).b4 (d).b6 S r hs hp h3 h4 hr
local notation "u₀" => coord W (π ^ (start + j)) π (d).b3 (d).b4 (d).b6 2
local notation "old" => olderGlobalTensorChart hπ data S j hj m hm
local notation "ext" => olderGlobalExteriorTensorChart hπ data S j hj m hm

omit [IsDomain R] [IsBezout R] in
/-- The full original conic has the empty scheme as its entire horizontal intersection. -/
theorem coefficientShearScaleOneConicHorizontal_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _)
      (PrincipalOpenTensor.inclusion S u₀) C := by
  rw [tensorShearScaleOneConicImmersion_eq_spec]
  exact PrincipalOpenVanishingIntersection.isPullback (f).toRingHom
    (tensorCoord W (π ^ (start + j)) π (d).b3 (d).b4 (d).b6 S 2)
    (tensorShearScaleOneConicMap_coord W (π ^ (start + j)) π
      (d).b3 (d).b4 (d).b6 S r hs hp h3 h4 hr 2)

/-- The entire conic/exterior intersection remains empty at every later global stage. -/
theorem coefficientShearScaleOneConicExterior_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) ext (C ≫ old) := by
  have H := coefficientShearScaleOneConicHorizontal_isPullback data S r j hj hs hp h3 h4 hr
  convert! H.paste_horiz (olderGlobalExteriorTensor_isPullback hπ data S j hj m hm) using 1
  exact Scheme.empty_ext _ _

/-- No original conic point belongs to the full preceding exterior after retention. -/
theorem coefficientShearScaleOneConicExterior_disjoint :
    Disjoint (Set.range ext) (Set.range (C ≫ old)) := by
  apply Scheme.isEmpty_pullback_iff.mp
  let E := (coefficientShearScaleOneConicExterior_isPullback
    hπ data S r j hj m hm hs hp h3 h4 hr).isoPullback
  exact E.symm.hom.homeomorph.isEmpty

local notation "y" => successiveOriginalY d
local notation "inf" => finiteInfinityTensorChart hπ data S (j + 1 + m) hm

omit [IsDomain R] [IsBezout R] in
/-- The original vertical function vanishes on the whole scale-one conic. -/
theorem coefficientShearScaleOneConic_originalY : f ((1 : S) ⊗ₜ[R] y) = 0 := by
  have H : (1 : S) ⊗ₜ[R] y =
      ((1 : S) ⊗ₜ[R] algebraMap R
        (Coordinate W (π ^ (start + j)) π (d).b3 (d).b4 (d).b6) (π ^ (start + j))) *
        (((1 : S) ⊗ₜ[R] coord W (π ^ (start + j)) π (d).b3 (d).b4 (d).b6 2) *
          ((1 : S) ⊗ₜ[R] coord W (π ^ (start + j)) π (d).b3 (d).b4 (d).b6 1)) := by
    simp only [successiveOriginalY, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rfl
  have hz : f ((1 : S) ⊗ₜ[R] u₀) = 0 :=
    tensorShearScaleOneConicMap_coord W (π ^ (start + j)) π
      (d).b3 (d).b4 (d).b6 S r hs hp h3 h4 hr 2
  rw [H, map_mul, map_mul, hz, zero_mul, mul_zero]

/-- The entire scale-one conic has empty infinity intersection at every later stage. -/
theorem coefficientShearScaleOneConicInfinity_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) inf (C ≫ old) := by
  have H : IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _)
      (PrincipalOpenTensor.inclusion S y) C := by
    rw [tensorShearScaleOneConicImmersion_eq_spec]
    exact PrincipalOpenVanishingIntersection.isPullback (f).toRingHom
      ((1 : S) ⊗ₜ[R] y)
      (coefficientShearScaleOneConic_originalY data S r j hj hs hp h3 h4 hr)
  convert! H.paste_horiz (olderGlobalTensor_infinity_isPullback hπ data S j hj m hm) using 1
  exact Scheme.empty_ext _ _

/-- The original scale-one conic remains disjoint from the entire infinity chart. -/
theorem coefficientShearScaleOneConicInfinity_disjoint :
    Disjoint (Set.range inf) (Set.range (C ≫ old)) := by
  apply Scheme.isEmpty_pullback_iff.mp
  let E := (coefficientShearScaleOneConicInfinity_isPullback
    hπ data S r j hj m hm hs hp h3 h4 hr).isoPullback
  exact E.symm.hom.homeomorph.isEmpty

end FLT.Mazur.WeierstrassDividedDepth
