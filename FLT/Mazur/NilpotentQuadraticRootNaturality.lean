/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NilpotentQuadraticRoot

/-!
# Constructed quadratic branches commute with arithmetic restriction

Uniqueness identifies the chosen small roots under every coefficient map
preserving the specified nilpotent ideals. This includes quotient restriction
maps; no compatible root system is an additional hypothesis.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.NilpotentQuadraticRoot
variable {R S : Type*} [CommRing R] [CommRing S]
  (I : Ideal R) (hI : IsNilpotent I) (J : Ideal S) (hJ : IsNilpotent J)
  (a b : R) (ha : IsUnit a) (hb : b ∈ I)

/-- Every coefficient map preserving the ideals preserves the constructed small root. -/
theorem root_map (f : R →+* S) (hf : I ≤ J.comap f) :
    f (root I hI a b ha hb) = root J hJ (f a) (f b) (ha.map f) (hf hb) := by
  apply root_unique J hJ (f a) (f b) (ha.map f)
  · exact hf (root_mem I hI a b ha hb)
  · exact root_mem J hJ (f a) (f b) (ha.map f) (hf hb)
  · simpa only [map_add, map_mul, map_pow] using
      congrArg f (root_equation I hI a b ha hb)
  · exact root_equation J hJ (f a) (f b) (ha.map f) (hf hb)

/-- The constructed root is independent of enlarging the nilpotent ideal. -/
theorem root_of_le (K : Ideal R) (hK : IsNilpotent K) (hIK : I ≤ K) :
    root I hI a b ha hb = root K hK a b ha (hIK hb) := by
  apply root_unique K hK a b ha
  · exact hIK (root_mem I hI a b ha hb)
  · exact root_mem K hK a b ha (hIK hb)
  · exact root_equation I hI a b ha hb
  · exact root_equation K hK a b ha (hIK hb)

end FLT.Mazur.NilpotentQuadraticRoot
