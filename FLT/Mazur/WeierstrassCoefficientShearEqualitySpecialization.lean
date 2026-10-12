/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootEqualityComponent
public import FLT.Mazur.WeierstrassCoefficientShearScaleOneEqualityComponent
public import FLT.Mazur.WeierstrassCoefficientShearTerminalLaurentSpecialization
public import FLT.Mazur.ProjectiveLineCoefficientMap
public import FLT.Mazur.ProjectiveLineScaledEndpointReversal
public import FLT.Mazur.WeierstrassDividedGlobalFiniteProper
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Coefficient specialization of independent equality-terminal projective components

The full terminal Laurent charts and separatedness identify the independently
glued projective components under the actual coefficient specialization.
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
variable (T : Type u) [Field T] [Algebra R T] (f : S →ₐ[R] T) (t : T)
  (gs : algebraMap R T (π ^ (start + j)) = 0)
  (gp : algebraMap R T π = 0)
  (g3 : algebraMap R T (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3 = 0)
  (g4 : algebraMap R T (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4 = 0)
  (gc : IsUnit (algebraMap R T (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6))
  (ht : t ^ 2 + algebraMap R T W.a₁ * t - algebraMap R T W.a₂ = 0)
  (b : Tˣ) (hb : (b : T) = (rootShearCurve (W.map (algebraMap R T)) t).a₁)
  (hrt : f r = t)
local notation "gsNext" => show algebraMap R T (π ^ (start + (j + 1))) = 0 from by
  rw [← Nat.add_assoc, pow_succ, map_mul, gp, mul_zero]
local notation "M" => coefficientShearSpecialization hπ data S T r t (j + 1) hj f
local notation "p" => Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f.toRingHom))
include hrt

local notation "P" => ProjectiveLine.coefficientMap f.toRingHom
local notation "base" => coefficientShearGluedStructure hπ data S r (j + 1) hj

/-- The entire root equality terminal specializes with its original projective parameter. -/
@[reassoc] theorem coefficientShearRootEqualityComponent_specialization :
    coefficientShearRootEqualityComponent
        hπ data T t j hj gs gp g3 g4 gc ht b hb ≫ M =
      P ≫ coefficientShearRootEqualityComponent
        hπ data S r j hj hs hp h3 h4 hc hr a ha := by
  let _ : IsSeparated base := by
    unfold coefficientShearGluedStructure
    infer_instance
  apply ProjectiveLine.torus_hom_ext T base
  · rw [Category.assoc, coefficientShearSpecialization_structure,
      coefficientShearRootEqualityComponent_structure_assoc, Category.assoc,
      coefficientShearRootEqualityComponent_structure, ProjectiveLine.coefficientMap_toBase]
  · rw [coefficientShearRootEqualityComponent_torus_assoc,
      ProjectiveLine.left_coefficientMap_assoc, ← Category.assoc,
      ProjectiveLine.overlapLeft_coefficient, Category.assoc,
      coefficientShearRootEqualityComponent_torus]
    exact coefficientShearSpecialization_terminalLaurent
      hπ data S r j hj hp h3 h4 hc hr a ha T f t gp g3 g4 gc ht b hb hrt

variable (hsOne : algebraMap R S (π ^ (start + j)) = 1)
  (gsOne : algebraMap R T (π ^ (start + j)) = 1)

/-- The scale-one equality terminal specializes with its original projective parameter. -/
@[reassoc] theorem coefficientShearScaleOneEqualityComponent_specialization :
    coefficientShearScaleOneEqualityComponent
        hπ data T t j hj gsOne gp g3 g4 gc ht b hb ≫ M =
      P ≫ coefficientShearScaleOneEqualityComponent
        hπ data S r j hj hsOne hp h3 h4 hc hr a ha := by
  let _ : IsSeparated base := by
    unfold coefficientShearGluedStructure
    infer_instance
  apply ProjectiveLine.torus_hom_ext T base
  · rw [Category.assoc, coefficientShearSpecialization_structure,
      coefficientShearScaleOneEqualityComponent_structure_assoc, Category.assoc,
      coefficientShearScaleOneEqualityComponent_structure, ProjectiveLine.coefficientMap_toBase]
  · rw [coefficientShearScaleOneEqualityComponent_torus_assoc,
      ProjectiveLine.left_coefficientMap_assoc, ← Category.assoc,
      ProjectiveLine.overlapLeft_coefficient, Category.assoc,
      coefficientShearScaleOneEqualityComponent_torus]
    exact coefficientShearSpecialization_terminalLaurent
      hπ data S r j hj hp h3 h4 hc hr a ha T f t gp g3 g4 gc ht b hb hrt

end FLT.Mazur.WeierstrassDividedDepth
