/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationFiniteLiftCover
public import FLT.Mazur.RelativeRelationPulledIdealCover
public import FLT.Mazur.SectionLiftSimultaneousCertificate

/-!
# A common finite principal cover for several closed invariant sections

The intersection of their actual multiplier ideals gives neighborhoods on
which all selected sections lift. Separate source certificates ensure that
this common cover still covers the compared boundary. No agreement between
the chosen lifts on distinct neighborhoods is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S S' : Scheme.{u}} {A U : Over S} {A' U' : Over S'}
  {p q : A ⟶ U} {p' q' : A' ⟶ U'}
  (e : CategoryTheory.EquivalenceRelation p q)
  (e' : CategoryTheory.EquivalenceRelation p' q')
  (g : U'.left ⟶ U.left) (r : A'.left ⟶ A.left)
  (hp : r ≫ p.left = p'.left ≫ g) (hq : r ≫ q.left = q'.left ≫ g)
  (W : Opens (Orbit e))
local notation "m" => invariantMap e e' g r hp hq
local notation "Wc" =>
  (Functor.obj (Opens.map (PresheafedSpace.Hom.base (LocallyRingedSpace.Hom.toHom m))) W)
local notation "φ" => invariantSectionPullback e e' g r hp hq W
set_option quotPrecheck false in
local notation "ιc" => CommRingCat.Hom.hom ((invariantInclusion e').hom.app (op Wc))
variable {ι : Type*} (v : ι → (invariantSheaf e').obj.obj
  (op ((Opens.map (invariantMap e e' g r hp hq).base).obj W))) (s : Finset ι)
/-- Common original invariant multipliers, with their source ring kept explicit. -/
def simultaneousClosedLiftIdeal : Ideal ((invariantSheaf e).obj.obj (op W)) :=
  s.inf (fun i ↦ closedLiftIdeal e e' g r hp hq W (v i))

local notation "I" => simultaneousClosedLiftIdeal e e' g r hp hq W v s
/-- The common principal lifting locus, as an open of the original orbit space. -/
def simultaneousLiftOpen : Opens (Orbit e) := sectionIdealOpen (ringedSpace e) W I

local notation "N" => simultaneousLiftOpen e e' g r hp hq W v s

/-- Individual source certificates ensure that the common multiplier locus covers the boundary. -/
theorem simultaneousLiftOpen_boundary_cover
    (hWc : IsAffineOpen (pullOpen e' Wc).val)
    (hv : ∀ i ∈ s, v i ∈ sourceCertifiedSections φ ιc) :
    (Opens.map (m).base).obj N = Wc := by
  apply (preimage_sectionIdealOpen_eq_iff_sourceIdeal_top e e' g r hp hq W I hWc).mpr
  exact simultaneousSectionLiftIdeal_map_eq_top φ ιc v s hv

/-- One finite principal cover carries actual lifts of all selected sections on every member. -/
theorem simultaneousLiftOpen_finite_affine_lifts [NoetherianSpace U.left]
    [IsClosedImmersion g] (hW : IsAffineOpen (pullOpen e W).val)
    (hR : IsCompact (p.left ⁻¹ᵁ (pullOpen e W).val : Set A.left)) :
    ∃ indices : Finset I, (N : Set (Orbit e)) =
        ⋃ a ∈ indices, (invariantPrincipal e W a.val : Set (Orbit e)) ∧
      ∀ a ∈ indices, IsAffineOpen (pullOpen e (invariantPrincipal e W a.val)).val ∧
        ∀ i ∈ s, ∃ b : (invariantSheaf e).obj.obj (op (invariantPrincipal e W a.val)),
          (m).c.app (op (invariantPrincipal e W a.val)) b =
            (invariantSheaf e').obj.map ((Opens.map (m).base).map
              (homOfLE (invariantPrincipal_le e W a.val))).op (v i) := by
  let _ : NoetherianSpace (ringedSpace e) := orbit_noetherianSpace e
  obtain ⟨indices, hindices⟩ := sectionIdealOpen_finite_cover (ringedSpace e) W I
  refine ⟨indices, hindices, fun a _ ↦
    ⟨invariantPrincipal_source_affine e W hW a.val, fun i hi ↦ ?_⟩⟩
  apply (mem_closedLiftIdeal_radical_iff e e' g r hp hq W (v i) hW hR a.val).mp
  apply Ideal.le_radical
  exact (mem_simultaneousSectionLiftIdeal φ v s a.val).mp a.property i hi

end FLT.Mazur.RelativeRelationOrbit
