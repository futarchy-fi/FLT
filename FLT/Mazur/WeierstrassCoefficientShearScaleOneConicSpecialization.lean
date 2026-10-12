/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneConic
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneConic
public import FLT.Mazur.WeierstrassCoefficientShearSpecialization
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Coefficient specialization of the separate scale-one retained conic

The full conic embedding commutes with its explicit coefficient map. This
retains incidence, signed slope, scale-one constant and the actual model.
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
  (j : ℕ) (hj : j + 1 ≤ n) (m : ℕ) (hm : j + 1 + m ≤ n)
  (hs : algebraMap R S (π ^ (start + j)) = 1) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨j + 1, by omega⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨j + 1, by omega⟩).b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (gs : algebraMap R T (π ^ (start + j)) = 1) (gp : algebraMap R T π = 0)
  (g3 : algebraMap R T (data ⟨j + 1, by omega⟩).b3 = 0)
  (g4 : algebraMap R T (data ⟨j + 1, by omega⟩).b4 = 0)
  (gt : t ^ 2 + algebraMap R T W.a₁ * t - algebraMap R T W.a₂ = 0)
local notation "a" => (rootShearCurve (W.map (algebraMap R S)) r).a₁
local notation "b" => (rootShearCurve (W.map (algebraMap R T)) t).a₁
local notation "c" => algebraMap R S (data ⟨j + 1, by omega⟩).b6
local notation "d" => algebraMap R T (data ⟨j + 1, by omega⟩).b6
local notation "CS" => coefficientShearRetainedScaleOneConic hπ data S r j hj m hm
  hs hp h3 h4 hr
local notation "CT" => coefficientShearRetainedScaleOneConic hπ data T t j hj m hm
  gs gp g3 g4 gt
local notation "M" => coefficientShearSpecialization hπ data S T r t (j + 1 + m) hm f
variable (hrt : f r = t)
local notation "ha" => rootShearTangent_coefficient W S r T f t hrt
local notation "hc" => f.commutes (data ⟨j + 1, by omega⟩).b6
local notation "p" => Spec.map (CommRingCat.ofHom (conicCoefficientMap f.toRingHom a c b d ha hc))

/-- The whole retained conic specializes by its actual incidence and signed slope coordinates. -/
theorem coefficientShearSpecialization_retainedScaleOneConic : CT ≫ M = p ≫ CS := by
  symm
  apply coefficientShearSpecialization_unique
  · rw [Category.assoc, coefficientShearRetainedScaleOneConic_structure,
      ← Category.assoc CT, coefficientShearRetainedScaleOneConic_structure]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext (conicCoefficientMap_scalar f.toRingHom a c b d ha hc)
  · rw [Category.assoc,
      coefficientShearRetainedScaleOneConic_projection hπ data S r j hj m hm,
      coefficientShearRetainedScaleOneConic_projection hπ data T t j hj m hm]
    rw [← Category.assoc, ← Spec.map_comp]
    congr 1
    congr 1
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom
      (originalShearScaleOneConicMap_coefficient W (π ^ (start + j)) π
        (data ⟨j + 1, by omega⟩).b3 (data ⟨j + 1, by omega⟩).b4
        (data ⟨j + 1, by omega⟩).b6 S r hs hp h3 h4 hr T f t gs gp g3 g4 gt hrt)

end FLT.Mazur.WeierstrassDividedDepth
