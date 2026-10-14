/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.KernelPairGenericEffectiveOpen
public import FLT.Mazur.MonomorphismFiniteEtaleCover

/-!
# Full generic kernel coverage by finite etale relation certificates

The required neighborhoods belong to the unrestricted candidate kernel.
Their finite covers map to the actual original relation. Descent produces
inverse charts and a dense effective target without a global unramifiedness
hypothesis on the candidate projection. Existence of the cover is not asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.KernelPairEffectiveOpen
set_option backward.isDefEq.respectTransparency false
variable {D A T : Scheme.{0}} (p q : D ⟶ A) (w : A ⟶ T) (h : p ≫ w = q ≫ w)
  [IsNoetherian A] [IsNoetherian T] [LocallyOfFinitePresentation w] [QuasiCompact w]
  [IrreducibleSpace T] [Mono (pullback.lift p q h)]
local notation "m" => pullback.lift p q h
local notation "K" => (pullback w w : Scheme)
local notation "v" => pullback.fst w w ≫ w
local instance genericEtaleCertificateKernelNoetherian : IsNoetherian K := ⟨⟩

/-- Finite etale relation certificates detect the entire generic kernel on its original base. -/
theorem targetOpen_nonempty_iff_finite_etale_certificates :
    (targetOpen p q w h : Set T).Nonempty ↔
      ∃ (ι : Type) (_ : Finite ι) (Z W : ι → Scheme.{0})
        (b : ∀ i, W i ⟶ K) (t : ∀ i, Z i ⟶ W i) (a : ∀ i, Z i ⟶ D),
        (∀ i, IsAffine (Z i) ∧ IsAffine (W i) ∧ Etale (b i) ∧ Etale (t i) ∧
          IsFinite (t i) ∧ Surjective (t i) ∧ a i ≫ m = t i ≫ b i) ∧
        ∀ x : K, v x = genericPoint T → ∃ i, x ∈ Set.range (b i) := by
  rw [targetOpen_nonempty_iff_genericFiber]
  constructor
  · intro hg
    obtain ⟨ι, hι, Z, W, b, t, a, H, hc⟩ :=
      MonomorphismOpenImage.exists_finite_etale_image_cover m
        {x : K | v x = genericPoint T} (NoetherianSpace.isCompact _)
        (fun x hx ↦ hg x hx) ⊤ (by intro x hx; trivial)
    refine ⟨ι, hι, Z, W, b, t, a, ?_, hc⟩
    intro i
    obtain ⟨hZ, hW, hb, ht, hf, hs, he, _, _⟩ := H i
    exact ⟨hZ, hW, hb, ht, hf, hs, he⟩
  · rintro ⟨ι, _, Z, W, b, t, a, H, hc⟩ x hx
    obtain ⟨i, hi⟩ := hc x hx
    obtain ⟨_, _, hb, ht, _, hs, he⟩ := H i
    let _ := hb
    let _ := ht
    let _ := hs
    exact MonomorphismOpenImage.etale_image_le_of_finite_cover m (b i) (t i) (a i) he hi

/-- Pointwise finite certificates suffice without replacing the nonreduced generic kernel. -/
theorem targetOpen_nonempty_of_generic_etale_lifts
    (hg : ∀ x : K, v x = genericPoint T →
      ∃ (Z : Scheme.{0}) (t : Z ⟶ K) (a : Z ⟶ D) (z : Z),
        Etale t ∧ a ≫ m = t ∧ t z = x) : (targetOpen p q w h : Set T).Nonempty := by
  apply (targetOpen_nonempty_iff_genericFiber p q w h).mpr
  intro x hx
  obtain ⟨Z, t, a, z, ht, he, hz⟩ := hg x hx
  let _ := ht
  rw [← hz]
  exact MonomorphismOpenImage.mem_locus_of_fppf_lift m t a he z

end FLT.Mazur.KernelPairEffectiveOpen
