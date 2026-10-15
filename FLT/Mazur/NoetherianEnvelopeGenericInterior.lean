/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EnvelopeVerticalGenerizations
public import FLT.Mazur.NoetherianClosedImageGenerizations
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Actual original interiors above generic coefficient points

Noetherianity makes every missing-envelope accumulation visible through an
actual excluded point over a generization. Vertical fullness then removes
this obstruction whenever the coefficient point has no strict generizations.
In particular this proves ORIGINAL interior membership above the generic
point of an irreducible coefficient scheme, without an open Artinian ground.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.EnvelopeVerticalGenerizations
open SchemeOpenEnvelope
universe u
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} (A V : Over S) [Etale V.hom] [QuasiCompact V.hom]
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)

omit [QuasiCompact V.hom] in
/-- Noetherianity of the full original envelope follows from its affine etale geometry. -/
theorem original_envelope_noetherian [IsAffine S] [IsAffine A.left] [IsAffine V.left]
    [IsLocallyNoetherian A.left] : NoetherianSpace (prod A V).left := by
  let _ : IsAffine (prod A V).left := IsAffine.of_isIso (Over.prodLeftIsoPullback A V).hom
  let _ : Etale π := MorphismProperty.of_isPullback
    (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd A V)).flip
    (inferInstanceAs (Etale V.hom))
  let _ := LocallyOfFiniteType.isLocallyNoetherian π
  let _ : IsNoetherian (prod A V).left := ⟨⟩
  infer_instance

variable [NoetherianSpace (prod A V).left] (O : (prod A V).left.Opens)

/-- If the coefficient has no strict generization, the original full fiber is interior. -/
theorem interior_of_no_strict_coefficient_generization (x : A.left)
    (hx : x ∈ fullFiberLocus π O)
    (hbase : ∀ s : S, s ⤳ A.hom x → s = A.hom x) :
    x ∈ fullFiberInterior π O := by
  change x ∈ interior (π '' (O : Set (prod A V).left)ᶜ)ᶜ
  rw [interior_compl]
  intro h
  obtain ⟨e, he, hs⟩ :=
    (NoetherianClosedImage.mem_closure_image_iff π (π).continuous O.isOpen.isClosed_compl x).mp h
  exact excluded_specialization_base_ne A V O hx e he hs
    (hbase _ (hs.map A.hom.continuous))

/-- Generic coefficient points have actual original neighborhoods, not only fiberwise opens. -/
theorem interior_over_generic_coefficient [IrreducibleSpace S] (x : A.left)
    (hx : x ∈ fullFiberLocus π O) (hg : A.hom x = genericPoint S) :
    x ∈ fullFiberInterior π O := by
  apply interior_of_no_strict_coefficient_generization A V O x hx
  intro s hs
  have hs' : s ⤳ genericPoint S := by rwa [hg] at hs
  exact (hs'.antisymm (genericPoint_specializes s)).eq.trans hg.symm

end FLT.Mazur.EnvelopeVerticalGenerizations
