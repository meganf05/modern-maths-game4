import Game.Metadata

World "Equations"
Level 1

Title "Reflexivity"

Introduction "The `rfl` principle (short for reflexivity) can be used to prove any statement of the form
`?X = ?X`. Here, I use `?X` to stand in for any expression of any type.
It could be `8 + 9` or `a * b` or `\"adele\"` or whatever.

Below, you are asked to prove `x + y = x + y`, where `x` and `y` are natural numbers.
The word `sorry` between the `begin` and `end` lines below asks Lean not to give an error message if a
proof isn't complete. You'll see a <span style=\"color:orange\">warning</span> message in the
bottom-right hand pane. This indicates you shouldn't trust the proof just yet, as it uses `sorry`!

Delete `sorry` (using the backspace key on your keyboard). In the right-hand pane you'll see:
```
x y : ℕ
⊢ x + y = x + y
```

Here, `x y : ℕ` is the *context*, the set of things you know. In this case, you know `x` and `y`
are natural numbers.

The *target* is `⊢ x + y = x + y`. The `⊢` symbol can be read 'to prove'. So your target is
to prove `x + y = x + y`.

The bottom part of the right-hand pane shows an <span style=\"color:red\">error</span>  message:
tactic failed, there are unsolved goals. Don't panic! It's just telling you that you haven't yet
proved the result.

Your task is to replace `sorry` with `from rfl,`. Note the comma at the end of the line!
If you're successful, Lean will respond with the message `no goals` or `Proof complete!`

In `from rfl`, the word `from` is a *tactic*. This tactic takes a proof term and closes a goal
if the provided proof term exactly matches the target. The list of tactics you've seen so far
is presented in the left-hand pane."

Statement (h : x = 2) (g: y = 4) : x + x = y := by
  Hint "You can either start using `{h}` or `{g}`."
  Branch
    rw [g]
    Hint "You should use `{h}` now."
    rw [h]
  rw [h]
  Hint "You should use `{g}` now."
  rw [g]

Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

NewTactic rw rfl
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
