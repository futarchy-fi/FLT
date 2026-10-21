/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroSecantCoverage

/-!
# Zero-depth coverage at a supplied input index

Isolate transport of the depth equality before introducing the dependent
full atlas pair. This keeps the original domain and all its source coordinates.
-/

@[expose] public noncomputable section
open AlgebraicGeometry IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  [CommRing S] [Algebra R S] {W : WeierstrassCurve R} {π : R} {m k : ℕ}
  (D : SplitNodeDepth W π m) (d : Data W π k)
  (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)

include D in
/-- A supplied zero depth gives the same full original-input secant coverage. -/
theorem suppliedSmoothSecantDomain_zeroDepth_mem (hk : k = 0) (hm : 0 < m)
    (p : PrimeSpectrum S) (hp : algebraMap R S π ∈ p.asIdeal)
    (hx : a (x W (π ^ k) d.b3 d.b4 d.b6) ∉ p.asIdeal)
    (hu : c (x W (π ^ k) d.b3 d.b4 d.b6) ∉ p.asIdeal)
    (hd : a (x W (π ^ k) d.b3 d.b4 d.b6) -
      c (x W (π ^ k) d.b3 d.b4 d.b6) ∉ p.asIdeal) :
    p ∈ suppliedSmoothSecantDomain d a c := by
  subst k
  exact suppliedSmoothSecantDomain_zero_mem D d a c hm p hp hx hu hd

end FLT.Mazur.WeierstrassDividedDepth
