/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionCoverDiscrepancy
public import FLT.Mazur.ModuleTensorPowerSection

/-!
# Gluing power sections from compatible scalar coefficients

Actual powers of the chart generators have precisely the transition factors
used to correct numerators. Compatible coefficients therefore glue in the
existing tensor-power sheaf, without postulating an extension object.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
variable {X : Scheme.{u}} {L : X.Modules}

/-- Scalar multiplication of a section scales its tensor power by the scalar power. -/
lemma tensorPowerSection_smul (U : X.Opens) (r : Γ(X, U)) (s : Γ(L, U)) (n : ℕ) :
    tensorPowerSection L U (r • s) n = r ^ n • tensorPowerSection L U s n := by
  induction n with
  | zero => simp [tensorPowerSection]
  | succ n ih =>
    dsimp only [tensorPowerSection]
    rw [ih]
    change (ModuleSheafTensor.pairing L (tensorPower L n)).app U (r • s)
      (r ^ n • tensorPowerSection L U s n) =
      r ^ (n + 1) • ((ModuleSheafTensor.pairing L (tensorPower L n)).app U s)
        (tensorPowerSection L U s n)
    simp only [map_smul, LinearMap.smul_apply, smul_smul]
    rw [mul_comm, ← pow_succ']

namespace SectionCover
variable {ι : Type v} (s : ι → Γ(L, ⊤))

/-- The actual power of the restricted chart generator. -/
abbrev powerFrame (N : ℕ) (i : ι) (U : X.Opens) : Γ(tensorPower L N, U) :=
  tensorPowerSection L U (L.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (s i)) N

/-- Power frames commute with restriction. -/
lemma powerFrame_restrict (N : ℕ) (i : ι) {U V : X.Opens} (h : U ≤ V) :
    (tensorPower L N).presheaf.map (homOfLE h).op (powerFrame s N i V) =
      powerFrame s N i U := by
  rw [tensorPowerSection_restrict]
  simp only [powerFrame, ← Functor.map_comp_apply, ← op_comp, homOfLE_comp]

/-- Changing a power frame multiplies it by the corresponding ratio power. -/
lemma powerFrame_change (N : ℕ) (j k : ι) (U : X.Opens) (hj : U ≤ chart s j) :
    ratio s j k U hj ^ N • powerFrame s N j U = powerFrame s N k U := by
  rw [← tensorPowerSection_smul, sectionRatioOn_smul]

/-- Compatible coefficients yield a global section of the actual tensor power. -/
theorem glue_powerSection (hcover : ⨆ i, chart s i = ⊤) (N : ℕ)
    (b : ∀ j, Γ(X, chart s j)) (hb : ∀ j k, discrepancy s N b j k = 0) :
    ∃ σ : Γ(tensorPower L N, ⊤), ∀ j,
      (tensorPower L N).presheaf.map (homOfLE (show chart s j ≤ ⊤ from le_top)).op σ =
        b j • powerFrame s N j (chart s j) := by
  let G := tensorPower L N
  let t := fun j ↦ b j • powerFrame s N j (chart s j)
  have ht (j k : ι) : G.presheaf.map (homOfLE inf_le_left).op (t j) =
      G.presheaf.map (homOfLE inf_le_right).op (t k) := by
    dsimp only [t]
    erw [G.val.map_smul, G.val.map_smul]
    change res inf_le_left (b j) •
      (tensorPower L N).presheaf.map (homOfLE inf_le_left).op (powerFrame s N j (chart s j)) =
      res inf_le_right (b k) •
      (tensorPower L N).presheaf.map (homOfLE inf_le_right).op (powerFrame s N k (chart s k))
    rw [powerFrame_restrict, powerFrame_restrict]
    have he := sub_eq_zero.mp (hb j k)
    change res inf_le_left (b j) =
      ratio s j k _ inf_le_left ^ N * res inf_le_right (b k) at he
    change res inf_le_left (b j) • powerFrame s N j _ =
      res inf_le_right (b k) • powerFrame s N k _
    rw [he, mul_comm, mul_smul, powerFrame_change]
  obtain ⟨σ, hσ, _⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨G.presheaf, G.isSheaf⟩ : TopCat.Sheaf Ab X)
    (chart s) ⊤ (fun _ ↦ homOfLE le_top) (by rw [hcover]) t ht
  exact ⟨σ, hσ⟩

end SectionCover
end FLT.Mazur.FCurve
