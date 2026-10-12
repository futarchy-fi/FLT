/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorComplementExactPowers
public import FLT.Mazur.FilteredPoleBasis
public import FLT.Mazur.GenusOneGroupPoleFunctions
public import FLT.Mazur.WeightedPoleMonomials

/-!
# Monomial bases from the original geometric group's point

Functions constructed from the original low-pole spaces have exact weighted
orders. They give bases of every positive pole space on that same complement.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GenusOneGroupCoordinates
open FCurve Module
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {k : Type} [Field k] [IsAlgClosed k]
  (G : Over (Spec (.of k))) [GrpObj G] [IsIntegral G.left] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom]
  (hd : topologicalKrullDim G.left = 1) (hc : HasConstantGlobalSections G.hom)
  (hg : curveGenus G.hom hd hc = 1)
  (s : 𝟙_ (Over (Spec (.of k))) ⟶ G) (hI : EffectiveCartier s.left.ker)

/-- Use the actual complement section ring on its bundled field module. -/
local instance poleBasisRing : CommRing (divisorComplementModule G.hom s.left.ker) :=
  inferInstanceAs (CommRing
    Γ((Scheme.Opens.toScheme (X := G.left) s.left.ker.support.compl), ⊤))

local notation "x" => genusOneGroupPoleFunction G hd hc hg s hI 1 (by decide)
local notation "y" => genusOneGroupPoleFunction G hd hc hg s hI 2 (by decide)
local notation "P" => divisorPoleSubmodule G.hom hI

/-- The actual ordered monomials in the constructed pole-two and pole-three functions. -/
def monomial (j : ℕ) : divisorComplementModule G.hom s.left.ker :=
  WeightedPoleMonomials.monomial x y j

/-- Products of the original chosen coordinates have their weighted upper bound. -/
theorem product_mem (a b : ℕ) : x ^ a * y ^ b ∈ P (2 * a + 3 * b) := by
  rw [mem_divisorPoleSubmodule]
  apply divisorPoleFunctions_mul hI
  · exact divisorPoleFunctions_pow hI
      ((mem_divisorPoleSubmodule G.hom hI 2 x).mp
        (genusOneGroupPoleFunction_spec G hd hc hg s hI 1 (by decide)).1) a
  · exact divisorPoleFunctions_pow hI
      ((mem_divisorPoleSubmodule G.hom hI 3 y).mp
        (genusOneGroupPoleFunction_spec G hd hc hg s hI 2 (by decide)).1) b

/-- Their positive weighted order is exact at the full original point divisor. -/
theorem product_not_mem (a b : ℕ) (hab : 0 < a + b) :
    x ^ a * y ^ b ∉ P (2 * a + 3 * b - 1) := by
  let e := sectionImageIso G.hom s.left s.w
  let _ : IsIntegral s.left.ker.subscheme := IsIntegral.of_isIso e.inv
  let _ : Subsingleton s.left.ker.subscheme := (Scheme.homeoOfIso e).injective.subsingleton
  have hx := genusOneGroupPoleFunction_spec G hd hc hg s hI 1 (by decide)
  have hy := genusOneGroupPoleFunction_spec G hd hc hg s hI 2 (by decide)
  simp only [mem_divisorPoleSubmodule] at hx hy ⊢
  exact divisorPoleFunctions_monomial_not_mem G.hom hI 2 3 (by decide) (by decide)
    hx.1 hy.1 hx.2 hy.2 a b hab

/-- Every listed monomial has its stated upper pole bound. -/
theorem monomial_mem (j : ℕ) :
    monomial G hd hc hg s hI j ∈ P (WeightedPoleMonomials.order j) := by
  rw [← WeightedPoleMonomials.weightedOrder]
  exact product_mem G hd hc hg s hI _ _

/-- Distinct weighted orders cannot collapse in the original function filtration. -/
theorem monomial_not_mem_lt (j d : ℕ) (h : d < WeightedPoleMonomials.order j) :
    monomial G hd hc hg s hI j ∉ P d := by
  intro hm
  have hw := WeightedPoleMonomials.weightedOrder j
  apply product_not_mem G hd hc hg s hI
    (WeightedPoleMonomials.xExponent j) (WeightedPoleMonomials.yExponent j) (by omega)
  exact divisorPoleSubmodule_mono G.hom hI (by omega) hm

/-- Each original monomial is a nonzero regular function. -/
theorem monomial_ne_zero (j : ℕ) : monomial G hd hc hg s hI j ≠ 0 := by
  by_cases hj : j = 0
  · subst j
    let _ := nontrivial_of_ne _ _
      (genusOneGroupPoleFunction_ne_zero G hd hc hg s hI 1 (by decide))
    exact (WeightedPoleMonomials.monomial_zero x y).trans_ne one_ne_zero
  intro hz
  apply monomial_not_mem_lt G hd hc hg s hI j 0
    (by simp only [WeightedPoleMonomials.order, ite_eq_right hj]; omega)
  rw [hz]
  exact (P 0).zero_mem

/-- The original positive pole space has basis 1,x,y,x²,xy,x³,... . -/
def monomialBasis (m : ℕ) [NeZero m] : Basis (Fin m) k (P m) :=
  FilteredPoleBasis.basisOfOrders P (divisorPoleSubmodule_mono G.hom hI) m m
    (fun j ↦ monomial G hd hc hg s hI j) (fun j ↦ WeightedPoleMonomials.order j)
    (fun _ _ h ↦ WeightedPoleMonomials.order_strictMono h)
    (fun j ↦ monomial_mem G hd hc hg s hI j)
    (fun j ↦ monomial_ne_zero G hd hc hg s hI j)
    (fun j d h ↦ monomial_not_mem_lt G hd hc hg s hI j d h)
    (WeightedPoleMonomials.order_le m)
    (genusOne_group_pole_finrank G hd hc hg s hI m (Nat.pos_of_neZero m))

/-- The basis vectors retain the original chosen coordinate functions. -/
theorem monomialBasis_apply (m : ℕ) [NeZero m] (j : Fin m) :
    (monomialBasis G hd hc hg s hI m j : divisorComplementModule G.hom s.left.ker) =
      monomial G hd hc hg s hI j :=
  FilteredPoleBasis.basisOfOrders_apply ..

end FLT.Mazur.GenusOneGroupCoordinates
