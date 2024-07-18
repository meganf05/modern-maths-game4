import GameServer.Commands

import Game.MyGroup.Definition

World "GroupDefinition"
Level 4
Title "Left inverse"

Introduction "
The left inverse $a^{-1}$ of a group element $a$ satisfies the property that $a^{-1} * a = 1$.
This property is `mul_left_inv`, the left multiplicative inverse.

*Note* to enter `⁻¹` in Lean, type `\\-1`.
"

/-- `mul_left_inv` is a proof that `a⁻¹ * a = 1`
-/
DefinitionDoc MyGroup.Group.mul_left_inv as "mul_left_inv"

NewDefinition MyGroup.Group.mul_left_inv

namespace MyGroup

open Group

variable {G : Type} [Group G]

/-- Let $a, b, c$ be elements of $G$. Show that $(a^{-1} * (b^{-1} * b)) * a = 1 $. -/
Statement (a b : G) : (a⁻¹ * (b⁻¹ * b)) * a = 1 := by
  Hint (hidden := true) "Try rewriting with `mul_left_inv`"
  rw [mul_left_inv]
  Hint (hidden := true) "Remember when Lean writes `x * y * z`, it means `(x * y) * z`. Now use an
  appropriate multiplicative identity rule. Not sure how to continue? Use [Proof Guide](https://chatgpt.com/g/g-sbJfmQ6te-proof-guide) to help!"
  rw [mul_one]
  rw [mul_left_inv]

Conclusion "
Great, you've just used the left multiplicative inverse. We'll learn the left multiplicative inverse
in the next level.
Click \"Leave World\" below to leave the Group Definition world and move on to the
next world.
"

end MyGroup
