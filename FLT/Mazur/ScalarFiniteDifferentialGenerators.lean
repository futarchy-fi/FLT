/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarDifferentialPolynomialAnnihilator

/-!
# Finite differential generators without finite algebra generation

Finite relative differentials have generators which are differentials of
actual source elements. This applies to essentially finite-type algebras,
even when the algebra itself needs infinitely many inverses as generators.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarFiniteDifferentialGenerators
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]

/-- Finite differentials have a finite generating family of actual source differentials. -/
theorem exists_generators [Module.Finite A (KaehlerDifferential R A)] :
    ∃ (n : ℕ) (z : Fin n → A),
      Submodule.span A (Set.range fun i ↦ KaehlerDifferential.D R A (z i)) = ⊤ := by
  classical
  have hfg : (Submodule.span A (Set.range (KaehlerDifferential.D R A))).FG := by
    rw [KaehlerDifferential.span_range_derivation]
    exact Module.Finite.fg_top
  obtain ⟨s, hs, hspan⟩ := Submodule.fg_span_iff_fg_span_finset_subset _ |>.mp hfg
  choose z hz using fun i : s ↦ hs i.property
  let e := Fintype.equivFin s
  refine ⟨Fintype.card s, z ∘ e.symm, ?_⟩
  have hr : Set.range (fun i ↦ KaehlerDifferential.D R A (z (e.symm i))) = s := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      dsimp only
      rw [hz]
      exact (e.symm i).property
    · intro hx
      refine ⟨e ⟨x, hx⟩, ?_⟩
      simpa only [Equiv.symm_apply_apply] using hz ⟨x, hx⟩
  simpa only [Function.comp_apply, hr, KaehlerDifferential.span_range_derivation] using
    hspan.symm

/-- Essential finite type supplies these generators without asserting finite algebra type. -/
theorem exists_generators_of_essFiniteType [Algebra.EssFiniteType R A] :
    ∃ (n : ℕ) (z : Fin n → A),
      Submodule.span A (Set.range fun i ↦ KaehlerDifferential.D R A (z i)) = ⊤ :=
  exists_generators

/-- A common annihilator of differential generators kills the full differential module. -/
theorem mem_annihilator {ι : Type} (z : ι → A)
    (hz : Submodule.span A (Set.range fun i ↦ KaehlerDifferential.D R A (z i)) = ⊤)
    (a : A) (ha : ∀ i, a • KaehlerDifferential.D R A (z i) = 0) :
    a ∈ Module.annihilator A (KaehlerDifferential R A) := by
  have h : a • (LinearMap.id : KaehlerDifferential R A →ₗ[A]
      KaehlerDifferential R A) = 0 := by
    apply LinearMap.ext_on (s := Set.range fun i ↦ KaehlerDifferential.D R A (z i)) hz
    rintro _ ⟨i, rfl⟩
    exact ha i
  exact Module.mem_annihilator.mpr (fun m ↦ LinearMap.congr_fun h m)

end FLT.Mazur.ScalarFiniteDifferentialGenerators
