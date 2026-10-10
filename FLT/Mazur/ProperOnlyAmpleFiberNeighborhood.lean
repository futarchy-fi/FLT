/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleOpenAffineRecovery
public import FLT.Mazur.ProperAmpleFiberEnvelope
public import FLT.Mazur.ProperAmpleFiberNeighborhood

/-!
# Ample fiber neighborhoods for proper families

A proper family need not be finitely presented. Extend its specified line
and ample fiber to a constructed finite-presentation envelope, spread there,
and pull the neighborhood back through the closed recovery immersion.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.Approximation

namespace FLT.Mazur.FCurve

/-- A proper family over a spectrum has an ample neighborhood of the chosen ample fiber. -/
theorem exists_ample_neighborhood_spectrum_proper {R : CommRingCat.{0}} {X : Scheme.{0}}
    (f : X ⟶ Spec R) [IsProper f] (s : Spec R) (L : X.Modules)
    (hL : LocallyFreeRankOne L) (hA : AmpleLineBundle ((pullback (f.fiberι s)).obj L)) :
    ∃ U : (Spec R).Opens, s ∈ U ∧ IsAffineOpen U ∧
      AmpleLineBundle ((pullback (f ⁻¹ᵁ U).ι).obj L) := by
  obtain ⟨Y, g, i, M, hg, hfp, hi, he, hM, ⟨e⟩, ha⟩ :=
    exists_proper_ampleFiber_finitelyPresented_closed_envelope f L hL s hA
  let _ := hg
  let _ := hfp
  let _ := hi
  obtain ⟨U, hsU, hU, hB⟩ := exists_ample_neighborhood_finitePresentation g s M hM ha
  refine ⟨U, hsU, hU, ?_⟩
  subst f
  have hC := ampleLineBundle_open_affine_recovery i M L e (g ⁻¹ᵁ U) hB
  simpa only [Scheme.Hom.comp_preimage] using hC

/-- An arbitrary affine base admits the proper-only ample fiber neighborhood theorem. -/
theorem exists_ample_neighborhood_affine_proper {X S : Scheme.{0}} [IsAffine S]
    (f : X ⟶ S) [IsProper f] (s : S) (L : X.Modules) (hL : LocallyFreeRankOne L)
    (hA : AmpleLineBundle ((pullback (f.fiberι s)).obj L)) :
    ∃ U : S.Opens, s ∈ U ∧ IsAffineOpen U ∧
      AmpleLineBundle ((pullback (f ⁻¹ᵁ U).ι).obj L) := by
  let q := f ≫ S.isoSpec.hom
  have hF := ampleLineBundle_fiber_baseIso f S.isoSpec s L hA
  obtain ⟨U, hsU, hU, ha⟩ :=
    exists_ample_neighborhood_spectrum_proper q (S.isoSpec.hom s) L hL hF
  refine ⟨S.isoSpec.hom ⁻¹ᵁ U, hsU, hU.preimage S.isoSpec.hom, ?_⟩
  simpa only [q, Scheme.Hom.comp_preimage] using ha

/-- Properness suffices to spread ampleness from a fiber, with no finite-presentation premise. -/
theorem exists_ample_neighborhood_proper {X S : Scheme.{0}}
    (f : X ⟶ S) [IsProper f] (s : S) (L : X.Modules) (hL : LocallyFreeRankOne L)
    (hA : AmpleLineBundle ((pullback (f.fiberι s)).obj L)) :
    ∃ W : S.Opens, s ∈ W ∧ IsAffineOpen W ∧
      AmpleLineBundle ((pullback (f ⁻¹ᵁ W).ι).obj L) := by
  obtain ⟨V, hV, hsV, _⟩ := exists_isAffineOpen_mem_and_subset (show s ∈ (⊤ : S.Opens)
    from trivial)
  let _ : IsAffine V.toScheme := hV
  have ha := ampleLineBundle_fiber_morphismRestrict f V ⟨s, hsV⟩ L hA
  obtain ⟨U, hsU, hU, hB⟩ := exists_ample_neighborhood_affine_proper
    (f ∣_ V) ⟨s, hsV⟩ ((pullback (f ⁻¹ᵁ V).ι).obj L) (hL.pullback _) ha
  let _ : IsAffine U.toScheme := hU
  exact ⟨V.ι ''ᵁ U, ⟨⟨s, hsV⟩, hsU, rfl⟩, .of_isIso (V.ι.isoImage U).inv,
    ampleLineBundle_baseOpenImage f V U L hB⟩

end FLT.Mazur.FCurve
