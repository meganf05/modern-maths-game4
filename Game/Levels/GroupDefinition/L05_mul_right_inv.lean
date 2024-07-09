import GameServer.Commands

import Game.MyGroup.Definition

World "GroupDefinition"
Level 5
Title "Right inverse"

Introduction "
The right inverse $b^{-1}$ of a group element $b$ satisfies the property that $b * b^{-1} = 1$.
This property is  `mul_right_inv`, the right multiplicative inverse.

*Note* to enter `⁻¹` in Lean, type `\\-1`.
"

/-- `mul_right_inv` is a proof that `b * b⁻¹  = 1`
-/
DefinitionDoc MyGroup.Group.mul_right_inv as "mul_right_inv"

NewDefinition MyGroup.Group.mul_right_inv

namespace MyGroup

open Group

variable {G : Type} [Group G]

/-- Let $a, b, c$ be elements of $G$. Show that $(b^{-1} * (a^{-1} * a)) * b = 1 $. -/
Statement (a b : G) : (b * (a * a⁻¹)) * b⁻¹ = 1 := by
Hint (hidden := true) "Try rewriting with `mul_right_inv`"
rw [mul_right_inv]
Hint (hidden := true) "Remember when Lean writes `x * y * z`, it means `(x * y) * z`. Now use an
appropriate multiplicative identity rule"
rw [mul_one]
rw [mul_right_inv]

Conclusion "
Excellent. Well done! Click for the next level.
"
end MyGroup
