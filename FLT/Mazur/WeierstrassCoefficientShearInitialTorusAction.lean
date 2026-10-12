/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearInitialSmooth
public import FLT.Mazur.WeierstrassCoefficientShearTorusSmoothOrbit
public import FLT.Mazur.WeierstrassRootShearUnitNaturality

/-!
# The actual torus action on original initial tensor points

The input uses the independently constructed original tensor embedding. Its
ordered tangent parameter multiplies under the actual full sheared action,
for points over arbitrary coefficient algebras.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type) [CommRing S] [Algebra R S] (r : S) (j : ℕ) (hj : j ≤ n)
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "s" => π ^ start
local notation "V" => W.map (algebraMap R S)
local notation "T" => ScalarExtension W s (Data.b3 d) (Data.b4 d) (Data.b6 d) S
variable (hs : algebraMap R S (π ^ start) = 1)
  (h3 : algebraMap R S (Data.b3 (data ⟨0, Nat.zero_lt_succ n⟩)) = 0)
  (h4 : algebraMap R S (Data.b4 (data ⟨0, Nat.zero_lt_succ n⟩)) = 0)
  (h6 : algebraMap R S (Data.b6 (data ⟨0, Nat.zero_lt_succ n⟩)) = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (W.map (algebraMap R S)).a₁ + 2 * r)
local notation "hc" => tensorOriginal_nodal_coefficients W s (Data.b3 d) (Data.b4 d)
  (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) S h3 h4 h6
local notation "q" => tensorShearScaleOneParameter W s (Data.b3 d) (Data.b4 d)
  (Data.b6 d) S r hs h3 h4 h6 hr
local notation "B" => coefficientShearSmoothEmbedding hπ data S r j hj
local notation "g" => coefficientShearGluedStructure hπ data S r j hj
local notation "t" => Over.hom (MultiplicativeGroupScheme.gm S)
variable {A : Type} [CommRing A] [Algebra S A]
  (F : ScalarExtension W (π ^ start) (Data.b3 (data ⟨0, Nat.zero_lt_succ n⟩))
    (Data.b4 (data ⟨0, Nat.zero_lt_succ n⟩))
    (Data.b6 (data ⟨0, Nat.zero_lt_succ n⟩)) S →ₐ[S] A)
local notation "qF" => Units.map (AlgHom.toMonoidHom' F) q
local notation "Q" => rootShearSmoothUnitInput V r a ha hr (hc).1 (hc).2.1 (hc).2.2 qF
local notation "v" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom F)) ≫
  coefficientShearInitialTensorChart hπ data S r j hj

/-- Every original tensor point has its actual mapped tangent-unit smooth presentation. -/
theorem coefficientShearInitialTensorPoint_smooth : v = (Q).left ≫ B := by
  rw [coefficientShearInitialTensorChart_smoothInput hπ data S r j hj
    hs h3 h4 h6 hr a ha, ← Category.assoc, tensorShearScaleOneSmoothInput_unit]
  rw [rootShearSmoothUnitInput_natural]
  rfl

variable (p : Aˣ)
local notation "u" => laurentUnitOverPoint (R := S) p

include hs h3 h4 h6 hr a ha in
/-- The actual torus parameter and original tensor chart point form an action-domain pair. -/
theorem coefficientShearInitialTensorPair_condition : (u).left ≫ t = v ≫ g := by
  rw [coefficientShearInitialTensorPoint_smooth hπ data S r j hj hs h3 h4 h6 hr a ha F,
    Category.assoc, coefficientShearSmoothEmbedding_structure]
  exact (u).w.trans (Q).w.symm

local notation "hpq" => coefficientShearInitialTensorPair_condition hπ data S r j hj
  hs h3 h4 h6 hr a ha F p

/-- The independent global torus action multiplies the original tensor chart's tangent ratio. -/
theorem coefficientShearTorusAction_initialTensorPoint :
    pullback.lift (u).left v hpq ≫
        coefficientShearTorusAction hπ data S r j hj a ha hr (hc).1 (hc).2.1 (hc).2.2 =
      (rootShearSmoothUnitInput V r a ha hr (hc).1 (hc).2.1 (hc).2.2 (p * qF)).left ≫ B := by
  have hv := coefficientShearInitialTensorPoint_smooth hπ data S r j hj
    hs h3 h4 h6 hr a ha F
  simp only [hv]
  exact coefficientShearTorusAction_smoothUnits hπ data S r j hj a ha hr
    (hc).1 (hc).2.1 (hc).2.2 p qF

end FLT.Mazur.WeierstrassDividedDepth
