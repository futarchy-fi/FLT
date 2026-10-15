/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PartialGroundEnvelopeInterior

/-!
# Local original neighborhoods from nonsurjective ground comparisons

An open source comparison only needs to hit the point being retained. The
image of its partial-chart full-fiber open constructs an actual original
neighborhood, without a global source cover or invariant norm coefficient.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeOpenEnvelope
universe u
variable {X Y Z : Scheme.{u}} (π : Y ⟶ X) (U : Y.Opens) (v : Z ⟶ X)
  (hv : IsOpenMap v) (hU : IsOpen (v ⁻¹' fullFiberLocus π U))

/-- The actual original open reached by full fibers in a local source comparison. -/
def localFullFiberOpen : X.Opens := ⟨v '' (v ⁻¹' fullFiberLocus π U), hv _ hU⟩

/-- The constructed open retains exactly the original full fibers hit by the comparison. -/
theorem localFullFiberOpen_coe :
    (localFullFiberOpen π U v hv hU : Set X) = fullFiberLocus π U ∩ Set.range v :=
  Set.image_preimage_eq_inter_range

include hv hU

/-- Every reached original full fiber belongs to the original maximal full interior. -/
theorem mem_fullFiberInterior_of_open_preimage (x : X)
    (hx : x ∈ fullFiberLocus π U) (hvx : x ∈ Set.range v) :
    x ∈ fullFiberInterior π U := by
  have hle : localFullFiberOpen π U v hv hU ≤ fullFiberInterior π U := by
    apply interior_maximal ?_ (localFullFiberOpen π U v hv hU).isOpen
    rw [localFullFiberOpen_coe]
    exact Set.inter_subset_left
  apply hle
  change x ∈ (localFullFiberOpen π U v hv hU : Set X)
  rw [localFullFiberOpen_coe]
  exact ⟨hx, hvx⟩

end FLT.Mazur.SchemeOpenEnvelope

namespace FLT.Mazur.SchemeTranslationNorm
open Approximation SchemeOpenEnvelope HilbertChart.AffineRestriction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R S : Type} [CommRing R] [CommRing S]
  (a : Spec (.of S) ⟶ Spec (.of R))
  (V : Over (Spec (.of R))) (W : Over (Spec (.of S)))
  (w : (Over.map a).obj W ⟶ V) (H : IsPullback w.left W.hom V.hom a)
  {A : Over (Spec (.of R))} {B : Over (Spec (.of S))}
  (u : (Over.map a).obj B ⟶ A) (hu : IsOpenMap u.left)
  {I : Type} [Finite I] (T : I → Over (Spec (.of S))) (t : ∀ i, T i ⟶ W)
  [∀ i, IsAffine (T i).left]
/-- The local ground comparison uses the given partial-chart structural algebras. -/
local instance partialLocalTranslationAlgebra (i : I) : Algebra S Γ((T i).left, ⊤) :=
  affineBaseSectionAlgebra (T i).hom
variable {ι : I → Type} [∀ i, Finite (ι i)]
  (b : ∀ i, Module.Basis (ι i) S Γ((T i).left, ⊤))
  (U : (prod A V).left.Opens)
  (ht : ∀ y : (prod B W).left, (fixedBaseEnvelopeMap a V W w u).left y ∉ U →
    ∃ i, ∃ z : (T i).left, (t i).left z = (prod.snd : prod B W ⟶ W).left y)
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)

include H hu b ht

/-- One original point lift suffices; the source comparison need not be globally surjective. -/
theorem mem_originalFullInterior_of_partialGroundLift (x : A.left)
    (hx : x ∈ fullFiberLocus π U) (hxlift : x ∈ Set.range u.left) :
    x ∈ fullFiberInterior π U :=
  mem_fullFiberInterior_of_open_preimage π U u.left hu
    (isOpen_preimage_originalFullFiber_of_partialGroundCover a V W w H u T t b U ht)
    x hx hxlift

omit [Finite I] in
/-- Local lifts suffice for arbitrary open partial families on affine changed envelopes. -/
theorem mem_originalFullInterior_of_affinePartialGroundLift
    [IsAffine B.left] [IsAffine W.left] (ho : ∀ i, IsOpen (Set.range (t i).left))
    (x : A.left) (hx : x ∈ fullFiberLocus π U) (hxlift : x ∈ Set.range u.left) :
    x ∈ fullFiberInterior π U := by
  apply mem_fullFiberInterior_of_open_preimage π U u.left hu ?_ x hx hxlift
  exact (congrArg IsOpen (fullFiberLocus_baseChange
    (fixedBaseEnvelopeMap_isPullback a V W w u H) U)).mp
      (isOpen_fullFiber_open_of_affine_partialTranslation B W T t
        ((fixedBaseEnvelopeMap a V W w u).left ⁻¹ᵁ U) ht ho b)

/-- The locally reached full fibers have one genuine denominator for any finite collection. -/
theorem exists_originalDenominator_of_partialGroundLifts [IsAffine A.left]
    (F : Set A.left) (hF : F.Finite) (hFU : F ⊆ fullFiberLocus π U)
    (hFlift : F ⊆ Set.range u.left) :
    ∃ r : Γ(A.left, ⊤), F ⊆ A.left.basicOpen r ∧ r ∈ denominatorIdeal (π).appTop.hom U := by
  apply exists_fullFiberInterior_coefficient π U F hF
  intro x hx
  exact mem_originalFullInterior_of_partialGroundLift a V W w H u hu T t b U ht x
    (hFU hx) (hFlift hx)

end FLT.Mazur.SchemeTranslationNorm
