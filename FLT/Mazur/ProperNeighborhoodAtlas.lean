/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PartialProperEnvelopeInterior

/-!
# A constructed atlas of proper neighborhoods over an unchanged base

The index consists of actual source opens whose structural morphisms are
proper. Their union and covering maps are constructed without supplying a
covering family. Properness is over the given base, not a branch-specific
coefficient refinement.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ProperNeighborhoodAtlas
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- All actual open neighborhoods proper over the unchanged target. -/
def Index := {U : X.Opens // IsProper (U.ι ≫ f)}

/-- The maximal open covered by these proper neighborhoods. -/
def locus : X.Opens := ⨆ i : Index f, i.val

/-- A point belongs to this locus exactly when it has an actual proper open neighborhood. -/
theorem mem_locus_iff (x : X) :
    x ∈ locus f ↔ ∃ U : X.Opens, x ∈ U ∧ IsProper (U.ι ≫ f) := by
  simp only [locus, TopologicalSpace.Opens.mem_iSup]
  constructor
  · rintro ⟨U, hx⟩
    exact ⟨U.val, hx, U.property⟩
  · rintro ⟨U, hx, hU⟩
    exact ⟨⟨U, hU⟩, hx⟩

/-- Each index supplies its original open subscheme. -/
def source (i : Index f) : Scheme.{u} := i.val.toScheme

/-- The chart map is the actual open inclusion. -/
def inclusion (i : Index f) : source f i ⟶ X := i.val.ι

instance inclusion_isOpenImmersion (i : Index f) : IsOpenImmersion (inclusion f i) :=
  inferInstanceAs (IsOpenImmersion i.val.ι)

instance projection_isProper (i : Index f) : IsProper (inclusion f i ≫ f) := i.property

/-- The canonical charts cover exactly the constructed proper-neighborhood locus. -/
theorem covers (x : X) :
    (∃ i : Index f, ∃ z : source f i, inclusion f i z = x) ↔ x ∈ locus f := by
  simp only [locus, TopologicalSpace.Opens.mem_iSup]
  constructor
  · rintro ⟨i, z, rfl⟩
    exact ⟨i, z.property⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, ⟨x, hi⟩, rfl⟩

/-- Proper structural morphisms supply the entire canonical atlas without any local choices. -/
theorem locus_eq_top [IsProper f] : locus f = ⊤ := by
  apply top_le_iff.mp
  intro x _
  apply (mem_locus_iff f x).mpr
  refine ⟨⊤, trivial, ?_⟩
  change IsProper (X.topIso.hom ≫ f)
  infer_instance

/-- Compact subsets of the constructed locus have finitely many actual proper neighborhoods. -/
theorem exists_finite_cover (K : Set X) (hK : IsCompact K) (h : K ⊆ locus f) :
    ∃ J : Finset (Index f), ∀ x ∈ K,
      ∃ i ∈ J, ∃ z : source f i, inclusion f i z = x := by
  obtain ⟨J, hJ⟩ := hK.elim_finite_subcover
    (fun i : Index f ↦ Set.range (inclusion f i))
    (fun i ↦ (inclusion f i).isOpenMap.isOpen_range) (by
      intro x hx
      obtain ⟨i, z, hz⟩ := (covers f x).mpr (h hx)
      exact Set.mem_iUnion.mpr ⟨i, z, hz⟩)
  refine ⟨J, fun x hx ↦ ?_⟩
  obtain ⟨i, hi, z, hz⟩ := Set.mem_iUnion₂.mp (hJ hx)
  exact ⟨i, hi, z, hz⟩

end FLT.Mazur.ProperNeighborhoodAtlas
