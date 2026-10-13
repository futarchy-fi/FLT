/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearScaleOneComponentRootChange
public import FLT.Mazur.WeierstrassCoefficientShearScaleOneComponentSpecialization
import all FLT.Mazur.WeierstrassCoefficientShearScaleOneComponentSpecialization
public import FLT.Mazur.WeierstrassCoefficientShearRootInitialSpecialization

/-!
# Semilinear exchange of the complete scaleone components

Coefficient specialization and companion-root transport exchange the entire
independent projective components with their signed reciprocal parameters.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S)
  (j : ℕ) (hj : j + 1 ≤ n) (hjNext : j + 2 ≤ n)
  (m : ℕ) (hm : j + 2 + m ≤ n)
variable (hs : algebraMap R S (π ^ (start + j)) = 1) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩).b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
variable (t : S) (b : Sˣ)
  (hb : (b : S) = (rootShearCurve (W.map (algebraMap R S)) t).a₁)
  (ht : t ^ 2 + algebraMap R S W.a₁ * t - algebraMap R S W.a₂ = 0)
  (hrt : r + t = -algebraMap R S W.a₁)
  (f : S →ₐ[R] S) (htr : f t = r)
local notation "M" => coefficientShearSpecialization hπ data S S t r (j + 2 + m) hm f
local notation "D" => coefficientShearRootChange hπ data S t r (j + 2 + m) hm
local notation "σ" => coefficientShearSpecialization hπ data S S r r (j + 2 + m) hm f
local notation "P" => ProjectiveLine.coefficientMap f.toRingHom

/-- Transport through the companion presentation gives the full retained-stage self-map. -/
@[reassoc] theorem coefficientShearScaleOneSelfSpecialization_rootTransport : M ≫ (D).hom = σ := by
  apply (coefficientShearGlued_isPullback hπ data S r (j + 2 + m) hm).hom_ext
  · rw [Category.assoc, coefficientShearRootChange_structure,
      coefficientShearSpecialization_structure, coefficientShearSpecialization_structure]
  · rw [Category.assoc, coefficientShearRootChange_projection,
      coefficientShearSpecialization_projection, coefficientShearSpecialization_projection]

include ht hb hrt htr

/-- The entire first retained component maps to its opposite under self-specialization. -/
@[reassoc] theorem coefficientShearScaleOneFirstComponent_semilinear :
    coefficientShearScaleOneFirstComponent
        hπ data S r j hj hjNext m hm hs hp h3 h4 hr a ha ≫ σ =
      P ≫ coefficientShearScaleOneSecondComponent
        hπ data S r j hj hjNext m hm hs hp h3 h4 hr a ha := by
  have hab : Units.map f.toRingHom b = a := by
    apply Units.ext
    change f (b : S) = (a : S)
    rw [hb, ha]
    exact rootShearTangent_coefficient W S t S f r htr
  rw [← coefficientShearScaleOneSelfSpecialization_rootTransport hπ data S r j m hm t f,
    ← Category.assoc,
    coefficientShearScaleOneFirstComponent_specialization
      hπ data S S f t r j hj hjNext m hm hs hp h3 h4 ht hs hp h3 h4 hr
      b hb a ha htr hab,
    Category.assoc,
    coefficientShearScaleOneFirstComponent_rootChange
      hπ data S t j hj hjNext m hm hs hp h3 h4 ht b hb r a ha hr
      (by rw [add_comm]; exact hrt)]

/-- The entire second retained component maps to its opposite under self-specialization. -/
@[reassoc] theorem coefficientShearScaleOneSecondComponent_semilinear :
    coefficientShearScaleOneSecondComponent
        hπ data S r j hj hjNext m hm hs hp h3 h4 hr a ha ≫ σ =
      P ≫ coefficientShearScaleOneFirstComponent
        hπ data S r j hj hjNext m hm hs hp h3 h4 hr a ha := by
  have hab : Units.map f.toRingHom b = a := by
    apply Units.ext
    change f (b : S) = (a : S)
    rw [hb, ha]
    exact rootShearTangent_coefficient W S t S f r htr
  rw [← coefficientShearScaleOneSelfSpecialization_rootTransport hπ data S r j m hm t f,
    ← Category.assoc,
    coefficientShearScaleOneSecondComponent_specialization
      hπ data S S f t r j hj hjNext m hm hs hp h3 h4 ht hs hp h3 h4 hr
      b hb a ha htr hab,
    Category.assoc,
    coefficientShearScaleOneSecondComponent_rootChange
      hπ data S t j hj hjNext m hm hs hp h3 h4 ht b hb r a ha hr
      (by rw [add_comm]; exact hrt)]

end FLT.Mazur.WeierstrassDividedDepth
