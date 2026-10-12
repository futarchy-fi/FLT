/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianLocalBasisSelection

/-!
# Spreading selected ambient columns to principal neighborhoods

At each coefficient prime a rank-d projective quotient admits d selected ambient
columns. The map from those same original columns becomes an isomorphism on a
principal neighborhood. No global quotient basis is chosen.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R M Q ι : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup Q] [Module R Q] {d : ℕ}

/-- The map whose columns are a prescribed finite family of quotient elements. -/
@[irreducible] def selectedColumnMap (v : Fin d → Q) : (Fin d → R) →ₗ[R] Q :=
  (Pi.basisFun R (Fin d)).constr R v

/-- Localization preserves the values of the original selected columns. -/
theorem selectedColumnMap_localized_basis (S : Submonoid R) (v : Fin d → Q) (i : Fin d) :
    LocalizedModule.map S (selectedColumnMap v)
      ((Pi.basisFun R (Fin d)).ofIsLocalizedModule (Localization S) S
        (LocalizedModule.mkLinearMap S (Fin d → R)) i) =
      LocalizedModule.mkLinearMap S Q (v i) := by
  simp only [Module.Basis.ofIsLocalizedModule_apply, LocalizedModule.mkLinearMap_apply,
    LocalizedModule.map_mk, selectedColumnMap, Module.Basis.constr_basis]

/-- If the localized selected columns are a basis, the localized column map is bijective. -/
theorem selectedColumnMap_localized_bijective (S : Submonoid R) (v : Fin d → Q)
    (c : Module.Basis (Fin d) (Localization S) (LocalizedModule S Q))
    (hc : ∀ i, c i = LocalizedModule.mkLinearMap S Q (v i)) :
    Function.Bijective (LocalizedModule.map S (selectedColumnMap v)) := by
  let b := (Pi.basisFun R (Fin d)).ofIsLocalizedModule (Localization S) S
    (LocalizedModule.mkLinearMap S (Fin d → R))
  have h : LocalizedModule.map S (selectedColumnMap v) =
      (b.repr.trans c.repr.symm).toLinearMap := by
    apply b.ext
    intro i
    rw [selectedColumnMap_localized_basis, ← hc]
    simp
  rw [h]
  exact (b.repr.trans c.repr.symm).bijective

/-- The quotient stalk basis consists of selected vectors from the original ambient basis. -/
theorem exists_selected_columns_atPrime [Module.Finite R Q] [Module.Projective R Q]
    (b : Module.Basis ι R M) (q : M →ₗ[R] Q) (hq : Function.Surjective q)
    (p : PrimeSpectrum R) (hd : Module.rankAtStalk Q p = d) :
    ∃ (a : Fin d ↪ ι)
      (c : Module.Basis (Fin d) (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl Q)),
      ∀ i, c i = LocalizedModule.mkLinearMap p.asIdeal.primeCompl Q (q (b (a i))) := by
  let S := p.asIdeal.primeCompl
  let L := Localization S
  let _ : Module.Free L (LocalizedModule S Q) := Module.free_of_flat_of_isLocalRing
  let bp := b.ofIsLocalizedModule L S (LocalizedModule.mkLinearMap S M)
  let qp := LocalizedModule.map S q
  obtain ⟨a, c, hc⟩ := exists_selected_quotient_basis bp qp
    (LocalizedModule.map_surjective S q hq) hd
  refine ⟨a, c, fun i ↦ ?_⟩
  rw [hc]
  change LocalizedModule.map S q
    ((b.ofIsLocalizedModule L S (LocalizedModule.mkLinearMap S M)) (a i)) = _
  rw [Module.Basis.ofIsLocalizedModule_apply]
  exact LocalizedModule.map_mk S q (b (a i)) 1

/-- Bijectivity of a fixed column map spreads without changing that map. -/
theorem exists_column_map_bijective_away [Module.Finite R M]
    [Module.FinitePresentation R Q] (l : M →ₗ[R] Q) (p : PrimeSpectrum R)
    (h : Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl l)) :
    ∃ r : R, r ∉ p.asIdeal ∧ Function.Bijective (LocalizedModule.map (.powers r) l) := by
  apply Module.FinitePresentation.exists_notMem_bijective l p.asIdeal
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl Q)
  exact (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective _ _).mpr h

/-- A fixed ambient selection gives an isomorphism on a neighborhood of each quotient prime. -/
theorem exists_selected_columns_away [Module.Finite R Q] [Module.Projective R Q]
    (b : Module.Basis ι R M) (q : M →ₗ[R] Q) (hq : Function.Surjective q)
    (p : PrimeSpectrum R) (hd : Module.rankAtStalk Q p = d) :
    ∃ (a : Fin d ↪ ι) (r : R), r ∉ p.asIdeal ∧
      Function.Bijective (LocalizedModule.map (.powers r)
        (selectedColumnMap (fun i ↦ q (b (a i))))) := by
  obtain ⟨a, c, hc⟩ := exists_selected_columns_atPrime b q hq p hd
  have hb := selectedColumnMap_localized_bijective p.asIdeal.primeCompl _ c hc
  let _ := Module.finitePresentation_of_projective R Q
  refine ⟨a, ?_⟩
  exact exists_column_map_bijective_away (M := Fin d → R)
    (selectedColumnMap (fun i ↦ q (b (a i)))) p hb

end FLT.Mazur.GrassmannianChart
