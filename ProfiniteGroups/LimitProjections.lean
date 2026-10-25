/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

/-!
# Projections of limits of profinite groups

The projection of the canonical limit cone evaluates a compatible family at its index.
This relates the categorical projection API to the coordinate API on `ProfiniteGrp.limit`.

## References

* Mathlib, `Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic` (the canonical cone and
  compatible-family model of the limit).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace ProfiniteGrp

variable {J : Type v} [SmallCategory J] (F : J ⥤ ProfiniteGrp.{max v u})

/-- The canonical cone projection is evaluation at the chosen coordinate. -/
-- Evaluate the projection before its concrete morphism and coercion are expanded.
@[simp↓ low] theorem limitCone_π_apply (j : J) (x : limit F) :
    (limitCone F).π.app j x = x.val j :=
  rfl

end ProfiniteGrp
