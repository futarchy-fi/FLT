/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegralCyclotomicCoordinates
public import FLT.Mazur.FiniteLocallyFreeDegreeCover

/-!
# Finite faithfully flat integral cyclotomic covers

The integral cyclotomic coordinate algebra supplies a finite locally free
cover of positive Euler-totient degree. Actual scheme pullbacks give covers
over arbitrary arithmetic tests, without inverting the root order.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.IntegralCyclotomicCover

open IntegralCyclotomicCoordinates

variable (n : ℕ)

/-- The actual integral cyclotomic scheme over the integer spectrum. -/
def model : Over (Spec (.of ℤ)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Coordinate n))))

/-- The integral cover has finite locally free degree equal to the Euler totient. -/
theorem degree : FCurve.FiniteLocallyFreeDegree (model n).hom n.totient :=
  FCurve.finiteLocallyFreeDegree_spec_of_basis ℤ (Coordinate n) n.totient (basis n)

instance finite : IsFinite (model n).hom := (degree n).1

instance flat : Flat (model n).hom := (degree n).2.1

instance locallyOfFinitePresentation : LocallyOfFinitePresentation (model n).hom :=
  (degree n).2.2.1

instance surjective [NeZero n] : Surjective (model n).hom := (degree n).surjective (rank_pos n)

/-- The arithmetic cover is the actual scheme pullback, including at primes dividing n. -/
def cover {S : Scheme} (g : S ⟶ Spec (.of ℤ)) : Over S :=
  (Over.pullback g).obj (model n)

/-- Every arithmetic test retains the same positive finite locally free degree. -/
theorem cover_degree {S : Scheme} (g : S ⟶ Spec (.of ℤ)) :
    FCurve.FiniteLocallyFreeDegree (cover n g).hom n.totient := (degree n).baseChange g

/-- These are actual fppf covers over every arithmetic test scheme. -/
theorem cover_fppf [NeZero n] {S : Scheme} (g : S ⟶ Spec (.of ℤ)) :
    Flat (cover n g).hom ∧ Surjective (cover n g).hom ∧
      LocallyOfFinitePresentation (cover n g).hom :=
  ⟨(cover_degree n g).2.1, (cover_degree n g).surjective (rank_pos n),
    (cover_degree n g).2.2.1⟩

end FLT.Mazur.IntegralCyclotomicCover
