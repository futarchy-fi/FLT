/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperGeometricAcyclicDirectImage
public import FLT.Mazur.ProperLineGeometricSectionRank

/-!
# The global rank-one open of a geometrically acyclic proper line family

Affine rank-one opens assemble through their common intrinsic section rank.
The construction is independent of charts and commutes with cartesian base
change whenever the new base is locally Noetherian.
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
  (hV : ∀ s : S, ∀ n, Subsingleton (ModuleH ((pullback (f.fiberι s)).obj L) (n + 1)))

include hL hV in
/-- On a geometrically acyclic proper flat line family, the intrinsic rank-one locus is open. -/
theorem isOpen_properLineFiberSectionRank_one :
    IsOpen {s : S | properLineFiberSectionRank f L s = 1} := by
  refine isOpen_iff_forall_mem_open.mpr fun s hs ↦ ?_
  obtain ⟨U, hU, hsU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show s ∈ (⊤ : S.Opens) from trivial)
  let _ : IsAffine U.toScheme := hU
  let _ : IsNoetherianRing Γ(U.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top U.toScheme⟩
  let N := (pullback (f ⁻¹ᵁ U).ι).obj L
  have hn := hL.pullback (f ⁻¹ᵁ U).ι
  have hv (t : U.toScheme) (n : ℕ) : Subsingleton
      (ModuleH ((pullback ((f ∣_ U).fiberι t)).obj N) (n + 1)) :=
    (properLine_fiber_vanishing_iff (isPullback_morphismRestrict f U).flip
      L hL t (n + 1)).mpr (hV (U.ι t) n)
  let V := properLineRankOneOpen (f ∣_ U) N hn
    (residueAlgebra_vanishing_of_geometric (f ∣_ U) N hn hv)
  have he (t : U.toScheme) : t ∈ V ↔ properLineFiberSectionRank f L (U.ι t) = 1 := by
    change t ∈ properLineRankOneOpen _ _ _ _ ↔ _
    rw [properLineRankOneOpen_geometric_iff,
      properLineFiberSectionRank_baseChange (isPullback_morphismRestrict f U).flip L hL]
  refine ⟨U.ι ''ᵁ V, ?_, (U.ι ''ᵁ V).isOpen, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact (he t).mp ht
  · exact ⟨⟨s, hsU⟩, (he ⟨s, hsU⟩).mpr hs, rfl⟩

/-- The actual global rank-one open, using the intrinsic section rank on the acyclic family. -/
def properLineGlobalRankOneOpen : S.Opens :=
  ⟨{s | properLineFiberSectionRank f L s = 1},
    isOpen_properLineFiberSectionRank_one f L hL hV⟩

/-- Membership has no chosen affine chart or trivialization. -/
lemma mem_properLineGlobalRankOneOpen (s : S) :
    s ∈ properLineGlobalRankOneOpen f L hL hV ↔ properLineFiberSectionRank f L s = 1 :=
  Iff.rfl

/-- The affine rank-one construction is the restriction of the intrinsic global construction. -/
theorem properLineGlobalRankOneOpen_eq_affine [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] :
    properLineGlobalRankOneOpen f L hL hV = properLineRankOneOpen f L hL
      (residueAlgebra_vanishing_of_geometric f L hL hV) := by
  ext s
  exact (properLineRankOneOpen_geometric_iff f L hL _ s).symm

/-- Independently assembled rank-one opens agree under any cartesian change of base. -/
theorem properLineGlobalRankOneOpen_baseChange {P T : Scheme.{0}} [IsLocallyNoetherian T]
    {p : P ⟶ X} {q : P ⟶ T} [IsProper q] [Flat q] {g : T ⟶ S}
    (h : IsPullback p q f g)
    (hW : ∀ t : T, ∀ n, Subsingleton
      (ModuleH ((pullback (q.fiberι t)).obj ((pullback p).obj L)) (n + 1))) :
    properLineGlobalRankOneOpen q ((pullback p).obj L) (hL.pullback p) hW =
      g ⁻¹ᵁ properLineGlobalRankOneOpen f L hL hV := by
  ext t
  exact congrArg (· = 1) (properLineFiberSectionRank_baseChange h L hL t) |>.to_iff

end FLT.Mazur.LineSectionBaseChange
