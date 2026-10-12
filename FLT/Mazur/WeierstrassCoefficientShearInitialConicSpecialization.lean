/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearInitialConicProjection
import all FLT.Mazur.WeierstrassCoefficientShearInitialConicProjection
public import FLT.Mazur.WeierstrassCoefficientShearSpecialization
import all FLT.Mazur.WeierstrassCoefficientShearInitialFiber

/-!
# Coefficient specialization of the complete initial conic

The full conic embedding commutes with its explicit coefficient map. This
retains incidence, signed slope, initial constant and the actual model.
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
  (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  (f : S →ₐ[R] T) (r : S) (t : T)
  (j : ℕ) (hj : j ≤ n)
  (hs : algebraMap R S (π ^ start) = 0)
  (h3 : algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (gs : algebraMap R T (π ^ start) = 0)
  (g3 : algebraMap R T (data ⟨0, Nat.zero_lt_succ n⟩).b3 = 0)
  (g4 : algebraMap R T (data ⟨0, Nat.zero_lt_succ n⟩).b4 = 0)
  (gt : t ^ 2 + algebraMap R T W.a₁ * t - algebraMap R T W.a₂ = 0)
local notation "a" => (rootShearCurve (W.map (algebraMap R S)) r).a₁
local notation "b" => (rootShearCurve (W.map (algebraMap R T)) t).a₁
local notation "c" => algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b6
local notation "d" => algebraMap R T (data ⟨0, Nat.zero_lt_succ n⟩).b6
local notation "CS" => coefficientShearInitialConic hπ data S r j hj hs h3 h4 hr
local notation "CT" => coefficientShearInitialConic hπ data T t j hj gs g3 g4 gt
local notation "M" => coefficientShearSpecialization hπ data S T r t j hj f
variable (hrt : f r = t)
local notation "ha" => rootShearTangent_coefficient W S r T f t hrt
local notation "hc" => f.commutes (data ⟨0, Nat.zero_lt_succ n⟩).b6
local notation "p" => Spec.map (CommRingCat.ofHom (conicCoefficientMap f.toRingHom a c b d ha hc))

/-- The whole initial conic specializes by its actual incidence and signed slope coordinates. -/
theorem coefficientShearSpecialization_initialConic : CT ≫ M = p ≫ CS := by
  symm
  apply coefficientShearSpecialization_unique
  · rw [Category.assoc, coefficientShearInitialConic_structure,
      ← Category.assoc CT, coefficientShearInitialConic_structure]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext (conicCoefficientMap_scalar f.toRingHom a c b d ha hc)
  · rw [Category.assoc,
      coefficientShearInitialConic_projection hπ data S r j hj,
      coefficientShearInitialConic_projection hπ data T t j hj]
    rw [← Category.assoc, ← Spec.map_comp]
    congr 1
    congr 1
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom
      (originalShearInitialConicMap_coefficient W (π ^ start)
        (data ⟨0, Nat.zero_lt_succ n⟩).b3 (data ⟨0, Nat.zero_lt_succ n⟩).b4
        (data ⟨0, Nat.zero_lt_succ n⟩).b6 S r hs h3 h4 hr T f t gs g3 g4 gt hrt)

end FLT.Mazur.WeierstrassDividedDepth
