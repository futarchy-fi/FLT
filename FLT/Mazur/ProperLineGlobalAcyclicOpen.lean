/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLineCoefficientFiberComparison

/-!
# The global positive-cohomology open of a proper flat line family

Affine coefficient opens agree with the intrinsic fiber condition. Their
images therefore assemble over every locally Noetherian base, and the
resulting open commutes with cartesian base change and open restriction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.LineSectionBaseChange
open FCurve

variable {X S : Scheme.{0}} [IsLocallyNoetherian S]
  (f : X ⟶ S) [IsProper f] [Flat f] (L : X.Modules) (hL : LocallyFreeRankOne L)

include hL in
/-- The intrinsic fiber-acyclic locus is open on an arbitrary locally Noetherian base. -/
theorem isOpen_properLineGeometricAcyclicLocus :
    IsOpen (properLineGeometricAcyclicLocus f L) := by
  refine isOpen_iff_forall_mem_open.mpr fun s hs ↦ ?_
  obtain ⟨U, hU, hsU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show s ∈ (⊤ : S.Opens) from trivial)
  let _ : IsAffine U.toScheme := hU
  let _ : IsNoetherianRing Γ(U.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top U.toScheme⟩
  let N := (pullback (f ⁻¹ᵁ U).ι).obj L
  let V := properLineAcyclicOpen (f ∣_ U) N (hL.pullback _)
  have he : (V : Set U.toScheme) = U.ι ⁻¹' properLineGeometricAcyclicLocus f L :=
    (properLineAcyclicOpen_coe (f ∣_ U) N (hL.pullback _)).trans
      (properLineGeometricAcyclicLocus_restrict f L hL U)
  refine ⟨U.ι ''ᵁ V, ?_, (U.ι ''ᵁ V).isOpen, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact (Set.ext_iff.mp he t).mp ht
  · exact ⟨⟨s, hsU⟩, (Set.ext_iff.mp he ⟨s, hsU⟩).mpr hs, rfl⟩

/-- The global open is defined by the actual geometric residue-fiber condition. -/
def properLineGlobalAcyclicOpen : S.Opens :=
  ⟨properLineGeometricAcyclicLocus f L, isOpen_properLineGeometricAcyclicLocus f L hL⟩

/-- Membership keeps every positive cohomology group of the original fiber. -/
lemma mem_properLineGlobalAcyclicOpen (s : S) :
    s ∈ properLineGlobalAcyclicOpen f L hL ↔ ∀ n,
      Subsingleton (ModuleH ((pullback (f.fiberι s)).obj L) (n + 1)) := Iff.rfl

/-- On an affine base the assembled global open is the previously constructed coefficient open. -/
theorem properLineGlobalAcyclicOpen_eq_affine [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] :
    properLineGlobalAcyclicOpen f L hL = properLineAcyclicOpen f L hL := by
  exact SetLike.coe_injective (properLineAcyclicOpen_coe f L hL).symm

/-- Independent constructions after cartesian base change give exactly the inverse-image open. -/
theorem properLineGlobalAcyclicOpen_baseChange {P T : Scheme.{0}} [IsLocallyNoetherian T]
    {p : P ⟶ X} {q : P ⟶ T} [IsProper q] [Flat q] {g : T ⟶ S}
    (h : IsPullback p q f g) :
    properLineGlobalAcyclicOpen q ((pullback p).obj L) (hL.pullback p) =
      g ⁻¹ᵁ properLineGlobalAcyclicOpen f L hL :=
  SetLike.coe_injective (properLineGeometricAcyclicLocus_baseChange h L hL)

/-- Every open chart is the restriction of the single intrinsic global cohomology open. -/
theorem properLineGlobalAcyclicOpen_restrict (U : S.Opens) :
    properLineGlobalAcyclicOpen (f ∣_ U) ((pullback (f ⁻¹ᵁ U).ι).obj L) (hL.pullback _) =
      U.ι ⁻¹ᵁ properLineGlobalAcyclicOpen f L hL :=
  properLineGlobalAcyclicOpen_baseChange f L hL (isPullback_morphismRestrict f U).flip

end FLT.Mazur.LineSectionBaseChange
