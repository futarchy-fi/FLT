/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentGenericExtension
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Residue coordinates for a generic ideal embedding

Annihilation by the maximal ideal equips the actual sheaf stalk with its residue
field action. Dimension one then supplies a linear identification with that
field, and a cyclic generator whose annihilator is exactly the maximal ideal.
These are the stalk calculations for Stacks 30.12.2 (01YE). The global ideal
embedding still requires the coherent annihilator subsheaf and common ideal
constructions; this file does not construct that embedding.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.FCurve.CoherentDevissage

universe u

namespace FLT.Mazur.CoherentGenericIdealEmbedding

variable {X : Scheme.{u}} (M : X.Modules) (x : X)

/-- The maximal ideal annihilates the given module stalk. -/
def StalkAnnihilated : Prop :=
  ∀ (r : X.presheaf.stalk x), r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) →
    ∀ m : M.presheaf.stalk x, r • m = 0

/-- The residue action is constructed on the original stalk, not on its quotient. -/
@[instance_reducible]
def residueModule (hM : StalkAnnihilated M x) :
    Module (X.residueField x) (M.presheaf.stalk x) :=
  (show Module.IsTorsionBySet (X.presheaf.stalk x) (M.presheaf.stalk x)
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) from fun m r ↦ hM r r.property m).module

/-- Restriction of the constructed residue action is the original stalk action. -/
lemma residue_smul (hM : StalkAnnihilated M x) (r : X.presheaf.stalk x)
    (m : M.presheaf.stalk x) :
    letI := residueModule M x hM
    (X.residue x) r • m = r • m := rfl

/-- Dimension one produces residue-field coordinates on the actual stalk. -/
def rankOneCoordinates (hM : StalkAnnihilated M x)
    (hd : letI := residueModule M x hM
      Module.finrank (X.residueField x) (M.presheaf.stalk x) = 1) :
    letI := residueModule M x hM
    X.residueField x ≃ₗ[X.residueField x] M.presheaf.stalk x := by
  letI := residueModule M x hM
  exact (Module.nonempty_linearEquiv_of_finrank_eq_one hd).some

/-- The image of one is a generator of the original stalk over its local ring. -/
theorem exists_cyclic_generator (hM : StalkAnnihilated M x)
    (hd : letI := residueModule M x hM
      Module.finrank (X.residueField x) (M.presheaf.stalk x) = 1) :
    ∃ m : M.presheaf.stalk x, m ≠ 0 ∧
      (∀ n : M.presheaf.stalk x, ∃ r : X.presheaf.stalk x, r • m = n) ∧
      ∀ r : X.presheaf.stalk x,
        r • m = 0 ↔ r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  let _ := residueModule M x hM
  let e := rankOneCoordinates M x hM hd
  refine ⟨e 1, ?_, ?_, ?_⟩
  · exact fun h ↦ one_ne_zero (e.injective (h.trans e.map_zero.symm))
  · intro n
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (e.symm n)
    refine ⟨r, ?_⟩
    rw [← residue_smul M x hM, ← e.map_smul]
    change e ((X.residue x) r * 1) = n
    rw [mul_one]
    exact (congrArg e hr).trans (e.apply_symm_apply n)
  · intro r
    rw [← residue_smul M x hM, ← e.map_smul]
    change e ((X.residue x) r * 1) = 0 ↔ _
    rw [mul_one, e.map_eq_zero_iff]
    exact Ideal.Quotient.eq_zero_iff_mem

/-- Under the dimension-one hypothesis the whole-stalk annihilator is maximal. -/
theorem annihilator_eq_maximalIdeal (hM : StalkAnnihilated M x)
    (hd : letI := residueModule M x hM
      Module.finrank (X.residueField x) (M.presheaf.stalk x) = 1) :
    Module.annihilator (X.presheaf.stalk x) (M.presheaf.stalk x) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  obtain ⟨m, _, _, hm⟩ := exists_cyclic_generator M x hM hd
  ext r
  exact ⟨fun hr ↦ (hm r).mp (Module.mem_annihilator.mp hr m),
    fun hr ↦ Module.mem_annihilator.mpr (hM r hr)⟩

/-- Any finite basis of the given residue stalk has exactly one element. -/
theorem multiplicity_one (hM : StalkAnnihilated M x)
    (hd : letI := residueModule M x hM
      Module.finrank (X.residueField x) (M.presheaf.stalk x) = 1)
    (r : ℕ) (b : letI := residueModule M x hM
      Module.Basis (Fin r) (X.residueField x) (M.presheaf.stalk x)) : r = 1 := by
  let _ := residueModule M x hM
  have hb := Module.finrank_eq_card_basis b
  simpa using hb.symm.trans hd

end FLT.Mazur.CoherentGenericIdealEmbedding
