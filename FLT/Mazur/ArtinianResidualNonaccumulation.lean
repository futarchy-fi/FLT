/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArtinianGroundEnvelopeInterior
public import FLT.Mazur.CommonGroundResidualGenerizations

/-!
# Residual nonaccumulation on locally Artinian common ground

For the FULL Cartesian envelope the excluded residual image is closed: its
source is closed and the entire envelope projection is finite. Thus a full
original fiber excludes all residual specializations, not merely equality
with their images. No Noetherianity of the source or properness of a selected
core is needed. Original interiors follow when the comparison is open.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.CommonGroundEnvelope
open SchemeOpenEnvelope ProperCoreResidualInterior
universe u
set_option backward.isDefEq.respectTransparency false
variable {S U : Scheme.{u}} (q : U ⟶ S) (A V : Over S)
  [IsLocallyArtinian U] [Etale V.hom] [QuasiCompact V.hom]
local notation "B" => changed q A
local notation "W" => changed q V
local notation "π" => Over.Hom.left (prod.fst : prod B W ⟶ B)
local notation "π₀" => Over.Hom.left (prod.fst : prod A V ⟶ A)
variable (T : (pullback V.hom q).Opens) (O : (prod A V).left.Opens)

/-- Every excluded residual image is closed on Artinian ground, for any chosen open core. -/
theorem artinian_residualImage_isClosed : IsClosed (residualImage q A V T O) := by
  let _ : Etale (W).hom := inferInstanceAs (Etale (pullback.snd V.hom q))
  let _ : QuasiCompact (W).hom := inferInstanceAs (QuasiCompact (pullback.snd V.hom q))
  let _ := ArtinianGroundEnvelope.projection_isFinite B W
  apply (π).isClosedMap
  exact (comparison q A V ⁻¹ᵁ O).isOpen.isClosed_compl.inter
    (envelopeCore q A V T).isOpen.isClosed_compl

/-- An original full fiber avoids the entire residual closure, not only the residual image. -/
theorem artinian_not_mem_residualClosure (x : (B).left)
    (hx : pullback.fst A.hom q x ∈ SchemeOpenEnvelope.fullFiberLocus π₀ O) :
    x ∉ closure (residualImage q A V T O) := by
  rw [(artinian_residualImage_isClosed q A V T O).closure_eq]
  rintro ⟨e, he, hp⟩
  have hf : x ∈ SchemeOpenEnvelope.fullFiberLocus π (comparison q A V ⁻¹ᵁ O) := by
    rw [CommonGroundEnvelope.fullFiberLocus]
    exact hx
  exact he.1 ((mem_fullFiberLocus π _ x).mp hf e hp)

/-- No excluded independent coordinate projects to a generization of a retained full fiber. -/
theorem artinian_residual_not_specializes (x : (B).left)
    (hx : pullback.fst A.hom q x ∈ SchemeOpenEnvelope.fullFiberLocus π₀ O)
    (e : (prod B W).left) (ho : comparison q A V e ∉ O)
    (ht : e ∉ envelopeCore q A V T) : ¬ π e ⤳ x := by
  intro he
  apply artinian_not_mem_residualClosure q A V T O x hx
  exact subset_closure
    (he.mem_closed (artinian_residualImage_isClosed q A V T O) ⟨e, ⟨ho, ht⟩, rfl⟩)

end FLT.Mazur.CommonGroundEnvelope
