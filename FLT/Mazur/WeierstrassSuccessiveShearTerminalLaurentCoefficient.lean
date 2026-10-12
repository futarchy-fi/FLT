/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearTerminalLaurentConic
public import FLT.Mazur.WeierstrassSuccessiveShearTerminalBranchCoefficient
public import FLT.Mazur.WeierstrassSplitNodalLaurentCoefficient

/-!
# Coefficient specialization of the full original terminal Laurent algebra

The original horizontal and vertical functions commute with Laurent coefficient
extension, retaining the root, tangent unit, and nonzero divided constant.
-/

@[expose] public noncomputable section
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassDividedDepth WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (π : R)
  (k : ℕ) (b3 b4 b6 : R) (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "D" => S ⊗[R] WeierstrassDilatation.Coordinate W (π ^ (k + 1)) b3 b4 b6
local notation "x" => WeierstrassDilatation.x W (π ^ (k + 1)) b3 b4 b6
local notation "y" => WeierstrassDilatation.y W (π ^ (k + 1)) b3 b4 b6
variable (hc : IsUnit (algebraMap R S b6))
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "E" => tensorShearTerminalLaurentEquiv W π k b3 b4 b6 S r hp h3 h4 hr hc a ha
open LaurentPolynomial

/-- The entire original integral divided equation in terminal Laurent coordinates. -/
def originalShearTerminalLaurentMap :
    WeierstrassDilatation.Coordinate W (π ^ (k + 1)) b3 b4 b6 →ₐ[R] S[T;T⁻¹] :=
  ((E).toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight

/-- The original horizontal function keeps both tangent factors. -/
theorem originalShearTerminalLaurentMap_x :
    originalShearTerminalLaurentMap W π k b3 b4 b6 S r hp h3 h4 hr hc a ha x =
      C (↑a⁻¹ : S) * (C (algebraMap R S b6) * T (-1) - T 1) :=
  tensorShearTerminalLaurent_x W π k b3 b4 b6 S r hp h3 h4 hr hc a ha

/-- The original vertical function keeps the arbitrary root shift. -/
theorem originalShearTerminalLaurentMap_y :
    originalShearTerminalLaurentMap W π k b3 b4 b6 S r hp h3 h4 hr hc a ha y =
      T 1 + C r * (C (↑a⁻¹ : S) * (C (algebraMap R S b6) * T (-1) - T 1)) :=
  tensorShearTerminalLaurent_y W π k b3 b4 b6 S r hp h3 h4 hr hc a ha

variable (L : Type u) [CommRing L] [Algebra R L] (f : S →ₐ[R] L) (t : L)
  (gp : algebraMap R L π = 0) (g3 : algebraMap R L b3 = 0)
  (g4 : algebraMap R L b4 = 0) (gc : IsUnit (algebraMap R L b6))
  (ht : t ^ 2 + algebraMap R L W.a₁ * t - algebraMap R L W.a₂ = 0)
  (b : Lˣ) (hb : (b : L) = (rootShearCurve (W.map (algebraMap R L)) t).a₁)
  (hrt : f r = t)
include hrt

/-- Coefficient change fixes every Laurent character in the full original terminal equation. -/
theorem originalShearTerminalLaurentMap_coefficient :
    (AddMonoidAlgebra.mapAlgHom ℤ f).comp
        (originalShearTerminalLaurentMap W π k b3 b4 b6 S r hp h3 h4 hr hc a ha) =
      originalShearTerminalLaurentMap W π k b3 b4 b6 L t gp g3 g4 ht gc b hb := by
  have hi : f (↑a⁻¹ : S) = (↑b⁻¹ : L) := by
    exact congrArg (fun u : Lˣ => (↑u⁻¹ : L))
      (terminalShearUnits_coefficient W S r a ha L f t b hb hrt)
  have Hc (z : S) : AddMonoidAlgebra.mapAlgHom ℤ f (C z) = C (f z) := by
    exact AddMonoidAlgebra.mapAlgHom_single f 0 z
  have HT (n : ℤ) : AddMonoidAlgebra.mapAlgHom ℤ f (T n) = T n := by
    change AddMonoidAlgebra.mapAlgHom ℤ f (.single n 1) = .single n 1
    rw [AddMonoidAlgebra.mapAlgHom_single, map_one]
  apply WeierstrassDilatation.hom_ext
  · simp only [AlgHom.comp_apply, originalShearTerminalLaurentMap_x,
      map_mul, map_sub, Hc, HT, hi, f.commutes]
  · simp only [AlgHom.comp_apply, originalShearTerminalLaurentMap_y,
      map_add, map_mul, map_sub, Hc, HT, hi, hrt, f.commutes]

end FLT.Mazur.WeierstrassSuccessiveX
