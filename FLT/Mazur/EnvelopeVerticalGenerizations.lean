/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArtinianGroundEnvelopeInterior

/-!
# Original fullness is stable under generization inside a coefficient fiber

On every residue-field fiber the entire translation becomes finite, so the
original full-fiber locus restricts to an open. A bad independent coordinate
can specialize toward a full fiber only while its coefficient point changes.
The base is arbitrary; no Artinian assumption is made on it or its opens.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EnvelopeVerticalGenerizations
open SchemeOpenEnvelope CommonGroundEnvelope
universe u
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} (A V : Over S) [Etale V.hom] [QuasiCompact V.hom]
  (O : (prod A V).left.Opens)
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)

/-- Every generization in the same coefficient fiber of an original full point remains full. -/
theorem full_of_specializes_same_base {x y : A.left}
    (hy : y ∈ SchemeOpenEnvelope.fullFiberLocus π O) (hxy : x ⤳ y)
    (hb : A.hom x = A.hom y) : x ∈ SchemeOpenEnvelope.fullFiberLocus π O := by
  let s := A.hom y
  let q := S.fromSpecResidueField s
  let B := changed q A
  let W := changed q V
  let x' : A.hom.fiber s := (A.hom.fiberHomeo s).symm ⟨x, hb⟩
  let y' : A.hom.fiber s := A.hom.asFiber y
  have hx' : A.hom.fiberι s x' = x := A.hom.fiberι_fiberHomeo_symm s ⟨x, hb⟩
  have hy' : A.hom.fiberι s y' = y := A.hom.fiberι_asFiber y
  have hs : x' ⤳ y' := (A.hom.fiberι s).isEmbedding.isInducing.specializes_iff.mp
    (by rwa [hx', hy'])
  let I := fullFiberInterior (prod.fst : prod B W ⟶ B).left (comparison q A V ⁻¹ᵁ O)
  have hI : (I : Set (B).left) =
      A.hom.fiberι s ⁻¹' SchemeOpenEnvelope.fullFiberLocus π O :=
    ArtinianGroundEnvelope.changed_interior_coe A V q O
  have hIy : y' ∈ I := by
    rw [← SetLike.mem_coe, hI]
    change A.hom.fiberι s y' ∈ SchemeOpenEnvelope.fullFiberLocus π O
    rwa [hy']
  have hIx := hs.mem_open I.isOpen hIy
  rw [hI] at hIx
  change A.hom.fiberι s x' ∈ SchemeOpenEnvelope.fullFiberLocus π O at hIx
  rwa [hx'] at hIx

/-- Every excluded specialization witness forces a strict change of coefficient point. -/
theorem excluded_specialization_base_ne {x : A.left}
    (hx : x ∈ SchemeOpenEnvelope.fullFiberLocus π O) (e : (prod A V).left)
    (he : e ∉ O) (hs : π e ⤳ x) : A.hom (π e) ≠ A.hom x := by
  intro hb
  exact he ((mem_fullFiberLocus π O (π e)).mp
    (full_of_specializes_same_base A V O hx hs hb) e rfl)

end FLT.Mazur.EnvelopeVerticalGenerizations
