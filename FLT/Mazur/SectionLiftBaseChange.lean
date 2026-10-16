/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatSectionLiftCertificate
public import FLT.Mazur.FaithfullyFlatSectionLift

/-!
# Base change of an unbundled boundary restriction and its source test

The algebra structures are built from the two original ring maps. These
wrappers keep the scalar structures consistent for geometric section rings
and expose actual tensor maps without assuming a quotient scheme exists.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.SectionLiftBaseChange
variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  (f : A →+* B) (g : B →+* C)

/-- The boundary ring with its original invariant scalars. -/
@[instance_reducible]
def boundaryAlgebra : Algebra A B := f.toAlgebra

/-- The original closed source with exactly the composite scalar map. -/
@[instance_reducible]
def sourceAlgebra : Algebra A C := (g.comp f).toAlgebra


/-- The original test map, viewed over the original invariant scalars. -/
def sourceHom :
    letI := boundaryAlgebra f
    letI := sourceAlgebra f g
    B →ₐ[A] C := by
  let _ := boundaryAlgebra f
  let _ := sourceAlgebra f g
  exact ⟨g, fun _ ↦ rfl⟩

variable (S : Type*) [CommRing S] [Algebra A S]

/-- The actual boundary ring after extending the original scalar ring. -/
abbrev boundaryRing :=
  letI := boundaryAlgebra f
  S ⊗[A] B

/-- The tested source ring after the same scalar extension. -/
abbrev sourceRing :=
  letI := sourceAlgebra f g
  S ⊗[A] C

/-- The full extended restriction map. -/
def restriction : S →+* boundaryRing f S :=
  letI := boundaryAlgebra f
  algebraMap S (S ⊗[A] B)

/-- The full extended test map retains the original source inclusion. -/
def testMap : boundaryRing f S →+* sourceRing f g S :=
  letI := boundaryAlgebra f
  letI := sourceAlgebra f g
  (FlatAlgebraEqualizer.tensorMap S (sourceHom f g)).toRingHom

/-- An original prescribed boundary section in the extended boundary ring. -/
def boundarySection (t : B) : boundaryRing f S :=
  letI := boundaryAlgebra f
  1 ⊗ₜ[A] t

variable [Module.FaithfullyFlat A S]

/-- Certification is reflected even when the new multipliers only exist after base change. -/
theorem certified_iff (t : B) :
    boundarySection f S t ∈ sourceCertifiedSections (restriction f S) (testMap f g S) ↔
      t ∈ sourceCertifiedSections f g :=
  by
    let _ := boundaryAlgebra f
    let _ := sourceAlgebra f g
    exact FlatSectionLiftCertificate.certified_iff (sourceHom f g) S t

/-- An extended finite identity constructs an original finite identity. -/
theorem certificate_descends (t : B)
    (h : ∃ a : sectionLiftIdeal (restriction f S) (boundarySection f S t) →₀ sourceRing f g S,
      a.sum (fun v b ↦ b * testMap f g S (restriction f S v.val)) = 1) :
    ∃ a : sectionLiftIdeal f t →₀ C,
      a.sum (fun v b ↦ b * g (f v.val)) = 1 :=
  by
    let _ := boundaryAlgebra f
    let _ := sourceAlgebra f g
    exact FlatSectionLiftCertificate.certificate_descends (sourceHom f g) S t h

/-- A genuine lift of the extended prescribed section descends to an original lift. -/
theorem lift_descends (t : B) (s : S) (hs : restriction f S s = boundarySection f S t) :
    ∃ a : A, f a = t := by
  let _ := boundaryAlgebra f
  apply (FaithfullyFlatSectionLift.exists_lift_iff (Algebra.linearMap A B) S t).mp
  refine ⟨s ⊗ₜ[A] (1 : A), ?_⟩
  simpa only [restriction, boundarySection, Algebra.TensorProduct.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply, LinearMap.lTensor_tmul,
    Algebra.linearMap_apply, map_one] using hs

end FLT.Mazur.SectionLiftBaseChange
