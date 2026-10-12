/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearEqualityRootChange
public import FLT.Mazur.WeierstrassCoefficientShearEqualitySpecialization

/-!
# Semilinear reflection of independent equality-terminal projective components

Compose the full coefficient and companion-root comparisons. The actual
self-specialization of the entire model restricts to coefficient change
followed by the scaled projective reversal, including both endpoints.
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
  (hc : IsUnit (algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6))
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

/-- The coefficient specialization and full root transport give the actual model self-map. -/
@[reassoc] theorem coefficientShearSelfSpecialization_rootTransport : M ≫ (D).hom = σ := by
  apply (coefficientShearGlued_isPullback hπ data S r (j + 1) hj).hom_ext
  · rw [Category.assoc, coefficientShearRootChange_structure,
      coefficientShearSpecialization_structure, coefficientShearSpecialization_structure]
  · rw [Category.assoc, coefficientShearRootChange_projection,
      coefficientShearSpecialization_projection, coefficientShearSpecialization_projection]

include hrt htr ht hb

/-- The positive-scale terminal reflects semilinearly with its original constant scale. -/
@[reassoc] theorem coefficientShearRootEqualityComponent_semilinear :
    coefficientShearRootEqualityComponent
        hπ data S r j hj hs hp h3 h4 hc hr a ha ≫ σ =
      ProjectiveLine.coefficientMap f.toRingHom ≫
        ProjectiveLine.scaledEndpointReversal S hc.unit ≫
          coefficientShearRootEqualityComponent
            hπ data S r j hj hs hp h3 h4 hc hr a ha := by
  rw [← coefficientShearSelfSpecialization_rootTransport hπ data S r j hj t f,
    ← Category.assoc,
    coefficientShearRootEqualityComponent_specialization
      hπ data S t j hj hs hp h3 h4 hc ht b hb
      S f r hs hp h3 h4 hc hr a ha htr,
    Category.assoc,
    coefficientShearRootEqualityComponent_rootChange
      hπ data S t j hj hs hp h3 h4 hc ht b hb r hr a ha
      (by rw [add_comm]; exact hrt)]

variable (hsOne : algebraMap R S (π ^ (start + j)) = 1)

/-- The scale-one terminal reflects semilinearly with its original constant scale. -/
@[reassoc] theorem coefficientShearScaleOneEqualityComponent_semilinear :
    coefficientShearScaleOneEqualityComponent
        hπ data S r j hj hsOne hp h3 h4 hc hr a ha ≫ σ =
      ProjectiveLine.coefficientMap f.toRingHom ≫
        ProjectiveLine.scaledEndpointReversal S hc.unit ≫
          coefficientShearScaleOneEqualityComponent
            hπ data S r j hj hsOne hp h3 h4 hc hr a ha := by
  rw [← coefficientShearSelfSpecialization_rootTransport hπ data S r j hj t f,
    ← Category.assoc,
    coefficientShearScaleOneEqualityComponent_specialization
      (hsOne := hsOne) (gsOne := hsOne) hπ data S t j hj hp h3 h4 hc ht b hb
      S f r hp h3 h4 hc hr a ha htr,
    Category.assoc,
    coefficientShearScaleOneEqualityComponent_rootChange
      (hsOne := hsOne) hπ data S t j hj hp h3 h4 hc ht b hb r hr a ha
      (by rw [add_comm]; exact hrt)]

end FLT.Mazur.WeierstrassDividedDepth
