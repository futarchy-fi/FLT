/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalExterior
public import FLT.Mazur.WeierstrassSuccessiveShearConicBoundary
public import FLT.Mazur.PrincipalOpenVanishingIntersection

/-!
# The full arbitrary-root conic misses its original preceding exterior

The actual tensor conic kills the entire horizontal boundary function.
The full empty intersection persists through every retained global embedding.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
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
variable (hs : algebraMap R S (π ^ (start + j)) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "C" => tensorShearConicImmersion W (π ^ (start + j)) π
  (d).b3 (d).b4 (d).b6 S r hs hp h3 h4 hr
local notation "f" => tensorShearConicMap W (π ^ (start + j)) π
  (d).b3 (d).b4 (d).b6 S r hs hp h3 h4 hr
local notation "u₀" => coord W (π ^ (start + j)) π (d).b3 (d).b4 (d).b6 2
local notation "old" => olderGlobalTensorChart hπ data S j hj m hm
local notation "ext" => olderGlobalExteriorTensorChart hπ data S j hj m hm

omit [IsDomain R] [IsBezout R] in
/-- The full original conic has the empty scheme as its entire horizontal intersection. -/
theorem coefficientShearConicHorizontal_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _)
      (PrincipalOpenTensor.inclusion S u₀) C := by
  rw [tensorShearConicImmersion_eq_spec]
  exact PrincipalOpenVanishingIntersection.isPullback (f).toRingHom
    (tensorCoord W (π ^ (start + j)) π (d).b3 (d).b4 (d).b6 S 2)
    (tensorShearConicMap_coord W (π ^ (start + j)) π
      (d).b3 (d).b4 (d).b6 S r hs hp h3 h4 hr 2)

/-- The entire conic/exterior intersection remains empty at every later global stage. -/
theorem coefficientShearConicExterior_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) ext (C ≫ old) := by
  have H := coefficientShearConicHorizontal_isPullback data S r j hj hs hp h3 h4 hr
  convert! H.paste_horiz (olderGlobalExteriorTensor_isPullback hπ data S j hj m hm) using 1
  exact Scheme.empty_ext _ _

/-- No original conic point belongs to the full preceding exterior after retention. -/
theorem coefficientShearConicExterior_disjoint :
    Disjoint (Set.range ext) (Set.range (C ≫ old)) := by
  apply Scheme.isEmpty_pullback_iff.mp
  let E := (coefficientShearConicExterior_isPullback
    hπ data S r j hj m hm hs hp h3 h4 hr).isoPullback
  exact E.symm.hom.homeomorph.isEmpty

end FLT.Mazur.WeierstrassDividedDepth
