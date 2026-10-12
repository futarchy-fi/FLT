/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearTerminalBranchProjection
public import FLT.Mazur.WeierstrassSuccessiveShearTerminalBranchCoefficient
public import FLT.Mazur.WeierstrassCoefficientShearSpecialization

/-!
# Coefficient specialization of complete terminal branches

The original integral projection and coefficient projection determine each
entire branch after specialization, including its terminal node origin.
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
variable (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4 = 0)
  (h6 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "hsNext" => show algebraMap R S (π ^ (start + (j + 1))) = 0 from by
  rw [← Nat.add_assoc, pow_succ, map_mul, hp, mul_zero]
variable (T : Type u) [Field T] [Algebra R T] (f : S →ₐ[R] T) (t : T)
  (gp : algebraMap R T π = 0)
  (g3 : algebraMap R T (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3 = 0)
  (g4 : algebraMap R T (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4 = 0)
  (g6 : algebraMap R T (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = 0)
  (ht : t ^ 2 + algebraMap R T W.a₁ * t - algebraMap R T W.a₂ = 0)
  (b : Tˣ) (hb : (b : T) = (rootShearCurve (W.map (algebraMap R T)) t).a₁)
  (hrt : f r = t)
local notation "gsNext" => show algebraMap R T (π ^ (start + (j + 1))) = 0 from by
  rw [← Nat.add_assoc, pow_succ, map_mul, gp, mul_zero]
local notation "M" => coefficientShearSpecialization hπ data S T r t (j + 1) hj f
local notation "p" => Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f.toRingHom))
include hrt

/-- The full first terminal branch specializes with its affine coordinate unchanged. -/
@[reassoc] theorem coefficientShearSpecialization_terminalFirst :
    coefficientShearTerminalFirstBranch hπ data T t (j + 1) hj
        gsNext g3 g4 g6 ht b hb ≫ M =
      p ≫ coefficientShearTerminalFirstBranch hπ data S r (j + 1) hj
        hsNext h3 h4 h6 hr a ha := by
  symm
  apply coefficientShearSpecialization_unique
  · rw [Category.assoc, coefficientShearTerminalFirstBranch_structure,
      coefficientShearTerminalFirstBranch_structure_assoc]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext (fun _ => Polynomial.map_C f.toRingHom)
  · rw [Category.assoc,
      coefficientShearTerminalFirstBranch_projection (hp := hp),
      coefficientShearTerminalFirstBranch_projection (hp := gp), ← Category.assoc,
      ← Spec.map_comp]
    congr 1
    congr 1
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom
      (originalShearTerminalFirstMap_coefficient W π (start + j)
        (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hp h3 h4 hr h6 a ha
        T f t gp g3 g4 g6 ht b hb hrt)

/-- The full second terminal branch specializes with its affine coordinate unchanged. -/
@[reassoc] theorem coefficientShearSpecialization_terminalSecond :
    coefficientShearTerminalSecondBranch hπ data T t (j + 1) hj
        gsNext g3 g4 g6 ht b hb ≫ M =
      p ≫ coefficientShearTerminalSecondBranch hπ data S r (j + 1) hj
        hsNext h3 h4 h6 hr a ha := by
  symm
  apply coefficientShearSpecialization_unique
  · rw [Category.assoc, coefficientShearTerminalSecondBranch_structure,
      coefficientShearTerminalSecondBranch_structure_assoc]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext (fun _ => Polynomial.map_C f.toRingHom)
  · rw [Category.assoc,
      coefficientShearTerminalSecondBranch_projection (hp := hp),
      coefficientShearTerminalSecondBranch_projection (hp := gp), ← Category.assoc,
      ← Spec.map_comp]
    congr 1
    congr 1
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom
      (originalShearTerminalSecondMap_coefficient W π (start + j)
        (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hp h3 h4 hr h6 a ha
        T f t gp g3 g4 g6 ht b hb hrt)

end FLT.Mazur.WeierstrassDividedDepth
