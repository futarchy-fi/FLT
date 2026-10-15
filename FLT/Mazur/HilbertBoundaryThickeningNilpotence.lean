/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryThickeningGeometry
public import FLT.Mazur.AffineEtaleNilpotentLift

/-!
# Nilpotent kernels and infinitesimal rigidity of the original boundary tower

The transition kernels are actual nilpotent ideal sheaves. Consequently maps
into an etale scheme with the same base map are determined by their restriction
to a lower boundary order. Affine etale charts over affine bases lift uniquely
across every transition. No affine quotient neighborhoods are assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.AffineIdealPower
set_option backward.isDefEq.respectTransparency false
variable {Y : Scheme.{u}} (J : Y.IdealSheafData)

/-- The defining ideal vanishes on its actual closed subscheme. -/
theorem comap_subscheme_self : J.comap J.subschemeι = ⊥ := by
  apply le_antisymm _ bot_le
  apply Scheme.IdealSheafData.le_map_iff_comap_le.mp
  rw [Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι]

variable {X : Scheme.{u}} [IsAffine X] (I : X.IdealSheafData)

omit [IsAffine X] in
/-- The transition kernel is the lower-order ideal pulled to the higher-order scheme. -/
theorem transition_ker {m n : ℕ} (h : m ≤ n) :
    (transition I h).ker = (I ^ m).comap (I ^ n).subschemeι := by
  have H : IsPullback (transition I h) (𝟙 _) (I ^ n).subschemeι
      (I ^ m).subschemeι :=
    IsPullback.of_vert_isIso_mono ⟨by rw [transition_ι, Category.id_comp]⟩
  rw [Scheme.IdealSheafData.comap,
    ← Scheme.Hom.ker_comp_of_isIso H.isoPullback.hom, H.isoPullback_hom_fst]

/-- A positive lower order gives a uniformly nilpotent transition kernel. -/
theorem transition_ker_pow {m n : ℕ} (h : m ≤ n) (hm : 0 < m) :
    (transition I h).ker ^ n = ⊥ := by
  rw [transition_ker, ← comap_pow, ← pow_mul]
  apply le_antisymm _ bot_le
  calc
    (I ^ (m * n)).comap (I ^ n).subschemeι ≤ (I ^ n).comap (I ^ n).subschemeι :=
      Scheme.IdealSheafData.comap_mono _ (power_le I (Nat.le_mul_of_pos_left n hm))
    _ = ⊥ := comap_subscheme_self _

/-- The actual scheme transition has nilpotent kernel, not only equal point support. -/
theorem transition_nilpotent {m n : ℕ} (h : m ≤ n) (hm : 0 < m) :
    IsNilpotent (transition I h).ker := ⟨n, transition_ker_pow I h hm⟩

end FLT.Mazur.AffineIdealPower

namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
omit [Etale V.hom]
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "O" => Scheme.Hom.opensRange (Over.Hom.left (toEnvelope f hL d V c k))
local notation "I" => boundaryIdealSheaf π O
local notation "B" n:max => originalThickenedSource f hL d V c k n

/-- Every original boundary transition has the explicit nilpotence exponent of its target. -/
theorem originalThickenedTransition_ker_pow {m n : ℕ} (h : m ≤ n) :
    (originalThickenedTransition f hL d V c k h).left.ker ^ (n + 1) = ⊥ :=
  AffineIdealPower.transition_ker_pow I (Nat.add_le_add_right h 1) (Nat.succ_pos m)

/-- The whole original tower consists of nilpotent closed immersions. -/
theorem originalThickenedTransition_nilpotent {m n : ℕ} (h : m ≤ n) :
    IsNilpotent (originalThickenedTransition f hL d V c k h).left.ker :=
  ⟨n + 1, originalThickenedTransition_ker_pow f hL d V c k h⟩

/-- Etale target maps are uniquely determined at a lower infinitesimal boundary order. -/
theorem originalThickenedTransition_etale_hom_ext {m n : ℕ} (h : m ≤ n)
    {Y Z : Scheme} (g : Y ⟶ Z) [Etale g] {a b : (B n).left ⟶ Y}
    (hab : (originalThickenedTransition f hL d V c k h).left ≫ a =
      (originalThickenedTransition f hL d V c k h).left ≫ b)
    (hbase : a ≫ g = b ≫ g) : a = b :=
  FormallyUnramified.hom_ext (originalThickenedTransition f hL d V c k h).left
    (originalThickenedTransition_nilpotent f hL d V c k h) g hab hbase

/-- Affine etale charts lift uniquely across every original boundary transition. -/
theorem originalThickenedTransition_etale_lift {m n : ℕ} (h : m ≤ n)
    {Y Z : Scheme} [IsAffine Y] [IsAffine Z] (g : Y ⟶ Z) [Etale g]
    (a : (B m).left ⟶ Y) (v : (B n).left ⟶ Z)
    (ha : (originalThickenedTransition f hL d V c k h).left ≫ v = a ≫ g) :
    ∃! b : (B n).left ⟶ Y,
      (originalThickenedTransition f hL d V c k h).left ≫ b = a ∧ b ≫ g = v :=
  AffineEtaleNilpotentLift.existsUnique_lift
    (originalThickenedTransition f hL d V c k h).left
    (originalThickenedTransition_nilpotent f hL d V c k h) g a v ha

end FLT.Mazur.HilbertChart.AffineRestriction
