/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleAffinePullback
public import FLT.Mazur.ModuleTensorPowerSection

/-!
# Positive powers preserve section generator opens

In local line-bundle coordinates, a pure tensor power has coordinate r^n.
For positive n its generator open is therefore unchanged, over arbitrary rings.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
variable {X : Scheme.{u}} {L : X.Modules}

/-- A trivialization induces compatible trivializations of natural tensor powers. -/
def tensorPowerTrivialization (e : L ≅ structureModule X) :
    ∀ n : ℕ, tensorPower L n ≅ structureModule X
  | 0 => Iso.refl _
  | n + 1 => ModuleSheafTensor.trivialTensorIso e (tensorPowerTrivialization e n)

/-- The coordinate of a pure tensor power is the corresponding scalar power. -/
lemma tensorPowerTrivialization_section (e : L ≅ structureModule X)
    (s : Γ(L, ⊤)) (n : ℕ) :
    (tensorPowerTrivialization e n).hom.app ⊤ (tensorPowerSection L ⊤ s n) =
      (show Γ(X, ⊤) from e.hom.app ⊤ s) ^ n := by
  induction n with
  | zero =>
    change (1 : Γ(X, ⊤)) = _
    exact (pow_zero _).symm
  | succ n hn =>
    change (ModuleSheafTensor.trivialTensorIso e (tensorPowerTrivialization e n)).hom.app ⊤
      (ModuleSheafTensor.pure _ _ ⊤ s (tensorPowerSection L ⊤ s n)) = _
    rw [ModuleSheafTensor.trivialTensorIso_pure]
    exact (congrArg (fun r : Γ(X, ⊤) ↦ (show Γ(X, ⊤) from e.hom.app ⊤ s) * r) hn).trans
      (pow_succ' (show Γ(X, ⊤) from e.hom.app ⊤ s) n).symm

/-- A positive power of a section of a trivial line bundle has the same generator open. -/
lemma tensorPowerSection_generatorOpen_of_trivial (e : L ≅ structureModule X)
    (s : Γ(L, ⊤)) {n : ℕ} (hn : 0 < n) :
    sectionGeneratorOpen (tensorPower L n) (tensorPowerSection L ⊤ s n) =
      sectionGeneratorOpen L s := by
  rw [← sectionGeneratorOpen_iso (tensorPowerTrivialization e n),
    tensorPowerTrivialization_section, sectionGeneratorOpen_structure,
    ← sectionGeneratorOpen_iso e, sectionGeneratorOpen_structure]
  exact X.basicOpen_pow _ hn

/-- Every positive tensor power of a line-bundle section has exactly the same open. -/
theorem tensorPowerSection_generatorOpen (hL : LocallyFreeRankOne L)
    (s : Γ(L, ⊤)) {n : ℕ} (hn : 0 < n) :
    sectionGeneratorOpen (tensorPower L n) (tensorPowerSection L ⊤ s n) =
      sectionGeneratorOpen L s := by
  ext x
  obtain ⟨U, hx, ⟨e⟩⟩ := hL x
  let P := (pullback U.ι).obj L
  let t := pullGlobal U.ι L s
  let e' : P ≅ structureModule U.toScheme :=
    ((restrictFunctorIsoPullback U.ι).app L).symm ≪≫ e
  have he : U.ι ⁻¹ᵁ sectionGeneratorOpen (tensorPower L n) (tensorPowerSection L ⊤ s n) =
      U.ι ⁻¹ᵁ sectionGeneratorOpen L s := by
    rw [← sectionGeneratorOpen_pullGlobal (hL.tensorPower n),
      ← sectionGeneratorOpen_pullGlobal hL]
    have h := sectionGeneratorOpen_iso (tensorPowerIso U.ι L n)
      (pullGlobal U.ι (tensorPower L n) (tensorPowerSection L ⊤ s n))
    rw [tensorPowerSection_pullback] at h
    exact h.symm.trans (tensorPowerSection_generatorOpen_of_trivial e' t hn)
  exact congrArg (fun V : U.toScheme.Opens ↦ (⟨x, hx⟩ : U.toScheme) ∈ V) he |>.to_iff

end FLT.Mazur.FCurve
