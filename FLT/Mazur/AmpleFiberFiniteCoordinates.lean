/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleFiberProjectiveCoordinates
public import FLT.Mazur.FiberAffineOpenBaseIso
public import FLT.Mazur.FiniteAffineBaseNeighborhood
public import FLT.Mazur.SectionProjectiveFiniteNeighborhood

/-!
# Finite projective coordinates near an ample fiber

The actual generating sections on the first affine neighborhood define a
projective morphism that is finite over a smaller affine neighborhood of
its spectrum. No finiteness or ampleness conclusion is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.ProjectiveSpace
open ModuleLineBundleTensorPullback

namespace FLT.Mazur.StalkBase

variable {X S : Scheme.{0}} [IsAffine S] [IsLocallyNoetherian S]
  [CompactSpace X] [X.IsSeparated] (f : X ⟶ S) [IsProper f] (s : S)
  {L : X.Modules} (hline : LocallyFreeRankOne L)
  (hL : AmpleLineBundle ((pullback (f.fiberι s)).obj L))

include hline hL

/-- Ample fiber sections give a finite projective map over a smaller affine spectrum open. -/
theorem exists_finite_projective_coordinate_neighborhood (N : ℕ) :
    ∃ (V : S.Opens) (hsV : s ∈ V) (hV : IsAffineOpen V)
      (n : ℕ), N ≤ n ∧ 0 < n ∧ ∃ (d : ℕ)
        (t : Fin (d + 1) → Γ(tensorPower ((pullback (f ⁻¹ᵁ V).ι).obj L) n, ⊤))
        (ht : ⨆ i, sectionGeneratorOpen
          (tensorPower ((pullback (f ⁻¹ᵁ V).ι).obj L) n) (t i) = ⊤),
      let q := (f ∣_ V) ≫ hV.isoSpec.hom
      ∃ U : (Spec Γ(S, V)).Opens, hV.isoSpec.hom ⟨s, hsV⟩ ∈ U ∧ IsAffineOpen U ∧
        IsFinite ((sectionProjectiveMorphism
          (tensorPower ((pullback (f ⁻¹ᵁ V).ι).obj L) n) d t ht
          (q.appTop.hom.comp (Scheme.ΓSpecIso Γ(S, V)).inv.hom)) ∣_
            (baseProjection Γ(S, V) (Fin (d + 1)) ⁻¹ᵁ U)) := by
  obtain ⟨V, hsV, hV, n, hn, hn0, d, t, ht, haff⟩ :=
    exists_projective_coordinate_neighborhood f s hline hL N
  let q := (f ∣_ V) ≫ hV.isoSpec.hom
  let M := tensorPower ((pullback (f ⁻¹ᵁ V).ι).obj L) n
  have ha (i : Fin (d + 1)) :
      IsAffineOpen (q.fiberι (hV.isoSpec.hom ⟨s, hsV⟩) ⁻¹ᵁ
        sectionGeneratorOpen M (t i)) :=
    Approximation.isAffineOpen_fiber_preimage_baseIso (f ∣_ V) hV.isoSpec
      ⟨s, hsV⟩ _ (haff i)
  obtain ⟨W, hsW, hW⟩ := sectionProjectiveMorphism_finite_neighborhood q M d t ht
    (hV.isoSpec.hom ⟨s, hsV⟩) ha
  obtain ⟨U, hsU, hU, _, hg⟩ := Approximation.exists_affine_finite_neighborhood
    (sectionProjectiveMorphism M d t ht
      (q.appTop.hom.comp (Scheme.ΓSpecIso Γ(S, V)).inv.hom))
    (baseProjection Γ(S, V) (Fin (d + 1))) _ W hsW
  exact ⟨V, hsV, hV, n, hn, hn0, d, t, ht, U, hsU, hU, hg⟩

end FLT.Mazur.StalkBase
