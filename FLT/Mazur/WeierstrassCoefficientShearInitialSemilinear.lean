/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootInitialRootChange
public import FLT.Mazur.WeierstrassCoefficientShearRootInitialSpecialization
/-!
# Semilinear exchange of the complete initial components

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
  (h1 : 1 ≤ n) (m : ℕ) (hm : 1 + m ≤ n)
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le h1))
variable (hs : algebraMap R S (π ^ start) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨1, Nat.lt_succ_of_le h1⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨1, Nat.lt_succ_of_le h1⟩).b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (g3 : algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b3 = 0)
  (g4 : algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b4 = 0)
  (g6 : algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b6 = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
variable (t : S) (b : Sˣ)
  (hb : (b : S) = (rootShearCurve (W.map (algebraMap R S)) t).a₁)
  (ht : t ^ 2 + algebraMap R S W.a₁ * t - algebraMap R S W.a₂ = 0)
  (hrt : r + t = -algebraMap R S W.a₁)
  (f : S →ₐ[R] S) (htr : f t = r)
local notation "M" => coefficientShearSpecialization hπ data S S t r (1 + m) hm f
local notation "D" => coefficientShearRootChange hπ data S t r (1 + m) hm
local notation "σ" => coefficientShearSpecialization hπ data S S r r (1 + m) hm f
local notation "P" => ProjectiveLine.coefficientMap f.toRingHom

/-- Transport through the companion presentation gives the full initial-stage self-map. -/
@[reassoc] theorem coefficientShearInitialSelfSpecialization_rootTransport : M ≫ (D).hom = σ := by
  apply (coefficientShearGlued_isPullback hπ data S r (1 + m) hm).hom_ext
  · rw [Category.assoc, coefficientShearRootChange_structure,
      coefficientShearSpecialization_structure, coefficientShearSpecialization_structure]
  · rw [Category.assoc, coefficientShearRootChange_projection,
      coefficientShearSpecialization_projection, coefficientShearSpecialization_projection]

include ht hb hrt htr

/-- The entire first initial component maps to its opposite under self-specialization. -/
@[reassoc] theorem coefficientShearRootInitialFirstComponent_semilinear :
    coefficientShearRootInitialFirstComponent
        hπ data S r h1 m hm hs hp h3 h4 hr g3 g4 g6 a ha ≫ σ =
      P ≫ coefficientShearRootInitialSecondComponent
        hπ data S r h1 m hm hs hp h3 h4 hr g3 g4 g6 a ha := by
  rw [← coefficientShearInitialSelfSpecialization_rootTransport hπ data S r m hm t f,
    ← Category.assoc,
    coefficientShearRootInitialFirstComponent_specialization
      hπ data S S f t r h1 m hm hs hp h3 h4 ht hs hp h3 h4 hr
      g3 g4 g6 g3 g4 g6 b hb a ha htr,
    Category.assoc,
    coefficientShearRootInitialFirstComponent_rootChange
      hπ data S t h1 m hm hs hp h3 h4 ht g3 g4 g6 b hb r a ha hr
      (by rw [add_comm]; exact hrt)]

/-- The entire second initial component maps to its opposite under self-specialization. -/
@[reassoc] theorem coefficientShearRootInitialSecondComponent_semilinear :
    coefficientShearRootInitialSecondComponent
        hπ data S r h1 m hm hs hp h3 h4 hr g3 g4 g6 a ha ≫ σ =
      P ≫ coefficientShearRootInitialFirstComponent
        hπ data S r h1 m hm hs hp h3 h4 hr g3 g4 g6 a ha := by
  rw [← coefficientShearInitialSelfSpecialization_rootTransport hπ data S r m hm t f,
    ← Category.assoc,
    coefficientShearRootInitialSecondComponent_specialization
      hπ data S S f t r h1 m hm hs hp h3 h4 ht hs hp h3 h4 hr
      g3 g4 g6 g3 g4 g6 b hb a ha htr,
    Category.assoc,
    coefficientShearRootInitialSecondComponent_rootChange
      hπ data S t h1 m hm hs hp h3 h4 ht g3 g4 g6 b hb r a ha hr
      (by rw [add_comm]; exact hrt)]

end FLT.Mazur.WeierstrassDividedDepth
