/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootTerminalRootChange
public import FLT.Mazur.WeierstrassCoefficientShearRootTerminalSpecialization
public import FLT.Mazur.WeierstrassCoefficientShearRootTerminalZeroRootChange
public import FLT.Mazur.WeierstrassCoefficientShearRootTerminalZeroSpecialization
public import FLT.Mazur.WeierstrassCoefficientShearEqualitySemilinear

/-!
# Full semilinear exchange before equality depth

The two independently completed terminal components exchange under actual
self-specialization in both incidence scale cases, with their full parameters.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S) (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
variable (hs : algebraMap R S (π ^ (start + j)) = 0)
  (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4 = 0)
  (h6 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "hsNext" => show algebraMap R S (π ^ (start + (j + 1))) = 0 from by
  rw [← Nat.add_assoc, pow_succ, map_mul, hp, mul_zero]
variable (t : S)
  (ht : t ^ 2 + algebraMap R S W.a₁ * t - algebraMap R S W.a₂ = 0)
  (b : Sˣ) (hb : (b : S) = (rootShearCurve (W.map (algebraMap R S)) t).a₁)
  (hrt : r + t = -algebraMap R S W.a₁)
local notation "C" => coefficientShearRootChange hπ data S r t (j + 1) hj
local notation "G" => coefficientShearGluedIso hπ data S t (j + 1) hj

local notation "base" => coefficientShearGluedStructure hπ data S t (j + 1) hj

variable (f : S →ₐ[R] S) (htr : f t = r)
local notation "M" => coefficientShearSpecialization hπ data S S t r (j + 1) hj f
local notation "D" => coefficientShearRootChange hπ data S t r (j + 1) hj
local notation "σ" => coefficientShearSpecialization hπ data S S r r (j + 1) hj f

include hrt htr ht hb

/-- The full first terminal component exchanges semilinearly in the positive-scale case. -/
@[reassoc] theorem coefficientShearRootTerminalFirstComponent_semilinear :
    coefficientShearRootTerminalFirstComponent
        hπ data S r j hj hs hp h3 h4 h6 hr a ha ≫ σ =
      ProjectiveLine.coefficientMap f.toRingHom ≫
        coefficientShearRootTerminalSecondComponent
          hπ data S r j hj hs hp h3 h4 h6 hr a ha := by
  rw [← coefficientShearSelfSpecialization_rootTransport hπ data S r j hj t f,
    ← Category.assoc,
    coefficientShearRootTerminalFirstComponent_specialization
      hπ data S t j hj hs hp h3 h4 h6 ht b hb
      S f r hs hp h3 h4 h6 hr a ha htr,
    Category.assoc,
    coefficientShearRootTerminalFirstComponent_rootChange
      hπ data S t j hj hs hp h3 h4 h6 ht b hb r hr a ha
      (by rw [add_comm]; exact hrt)]

/-- The full second terminal component exchanges semilinearly in the positive-scale case. -/
@[reassoc] theorem coefficientShearRootTerminalSecondComponent_semilinear :
    coefficientShearRootTerminalSecondComponent
        hπ data S r j hj hs hp h3 h4 h6 hr a ha ≫ σ =
      ProjectiveLine.coefficientMap f.toRingHom ≫
        coefficientShearRootTerminalFirstComponent
          hπ data S r j hj hs hp h3 h4 h6 hr a ha := by
  rw [← coefficientShearSelfSpecialization_rootTransport hπ data S r j hj t f,
    ← Category.assoc,
    coefficientShearRootTerminalSecondComponent_specialization
      hπ data S t j hj hs hp h3 h4 h6 ht b hb
      S f r hs hp h3 h4 h6 hr a ha htr,
    Category.assoc,
    coefficientShearRootTerminalSecondComponent_rootChange
      hπ data S t j hj hs hp h3 h4 h6 ht b hb r hr a ha
      (by rw [add_comm]; exact hrt)]

variable (hsOne : algebraMap R S (π ^ (start + j)) = 1)

/-- The full first terminal component exchanges semilinearly in the scale-one case. -/
@[reassoc] theorem coefficientShearRootTerminalZeroFirstComponent_semilinear :
    coefficientShearRootTerminalZeroFirstComponent
        hπ data S r j hj hsOne hp h3 h4 h6 hr a ha ≫ σ =
      ProjectiveLine.coefficientMap f.toRingHom ≫
        coefficientShearRootTerminalZeroSecondComponent
          hπ data S r j hj hsOne hp h3 h4 h6 hr a ha := by
  rw [← coefficientShearSelfSpecialization_rootTransport hπ data S r j hj t f,
    ← Category.assoc,
    coefficientShearRootTerminalZeroFirstComponent_specialization
      hπ data S t j hj hsOne hp h3 h4 h6 ht b hb
      S f r hsOne hp h3 h4 h6 hr a ha htr,
    Category.assoc,
    coefficientShearRootTerminalZeroFirstComponent_rootChange
      hπ data S t j hj hsOne hp h3 h4 h6 ht b hb r hr a ha
      (by rw [add_comm]; exact hrt)]

/-- The full second terminal component exchanges semilinearly in the scale-one case. -/
@[reassoc] theorem coefficientShearRootTerminalZeroSecondComponent_semilinear :
    coefficientShearRootTerminalZeroSecondComponent
        hπ data S r j hj hsOne hp h3 h4 h6 hr a ha ≫ σ =
      ProjectiveLine.coefficientMap f.toRingHom ≫
        coefficientShearRootTerminalZeroFirstComponent
          hπ data S r j hj hsOne hp h3 h4 h6 hr a ha := by
  rw [← coefficientShearSelfSpecialization_rootTransport hπ data S r j hj t f,
    ← Category.assoc,
    coefficientShearRootTerminalZeroSecondComponent_specialization
      hπ data S t j hj hsOne hp h3 h4 h6 ht b hb
      S f r hsOne hp h3 h4 h6 hr a ha htr,
    Category.assoc,
    coefficientShearRootTerminalZeroSecondComponent_rootChange
      hπ data S t j hj hsOne hp h3 h4 h6 ht b hb r hr a ha
      (by rw [add_comm]; exact hrt)]

end FLT.Mazur.WeierstrassDividedDepth
