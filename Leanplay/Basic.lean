import Mathlib.Tactic.Ring

-- Merge two sorted lists into a single sorted list
def merge_sorted : (acc xs ys : List Nat) -> List Nat
| acc, [], ys => acc ++ ys
| acc, xs, [] => acc ++ xs
| acc, x::xs, y::ys =>
  if x <= y then merge_sorted (acc ++ [x]) xs (y::ys )
  else merge_sorted (acc ++ [y]) ys (x::xs)
termination_by _ xs ys => xs.length + ys.length

-- if [x, ...] is sorted then [x, x, ...] is too
lemma pairwise_cons_repeat :
  {x : Nat} ->
  {xs : List Nat} ->
  (h : (x::xs).Pairwise LE.le) ->
  (x::x::xs).Pairwise LE.le
  := by
  intro x xs xxs_sorted
  have : ∀ x' ∈ xs, x ≤ x' := by rw [List.pairwise_cons] at xxs_sorted; exact xxs_sorted.left
  rw [List.pairwise_cons]
  simp [xxs_sorted]
  exact this

-- `merge_sorted` returns a permutation of its combined inputs
theorem merge_sorted_perm {acc xs ys: List Nat} : (acc ++ xs ++ ys).Perm (merge_sorted acc xs ys) := by
  unfold merge_sorted
  split; all_goals simp
  split
  . rw [List.append_cons, ← List.append_assoc]
    apply merge_sorted_perm
  . rename_i x xs y ys _
    apply List.Perm.trans _ merge_sorted_perm
    -- God, there's gotta be a more elegant way to prove this.
    rw [List.perm_iff_count]
    intro q
    simp [List.count_append, List.count_cons]
    repeat split
    all_goals ring_nf
termination_by sizeOf xs + sizeOf ys

-- If (acc, xs, ys) are ready to get smushed by mergesort, then the result is sorted
theorem merge_sorted_sorted :
    {xs ys acc: List Nat} ->
    (acc ++ xs).Pairwise LE.le ->
    (acc ++ ys).Pairwise LE.le ->
    (merge_sorted acc xs ys).Pairwise LE.le
    := by
  intro xs ys acc axxs_sorted ayys_sorted

  unfold merge_sorted
  split; any_goals assumption

  split
  on_goal 1 => rename_i x xs y ys x_le_y
  on_goal 2 => rename_i y ys x xs nx_le_y; rename' axxs_sorted=>ayys_sorted, ayys_sorted=>axxs_sorted; have x_le_y : x ≤ y := Nat.le_of_not_le nx_le_y

  -- I would like to refactor this into a lemma which we simply apply to each of the two identical subgoals,
  -- but I can't figure out how to do that without making the termination condition really annoying to prove.
  all_goals (
      apply merge_sorted_sorted; all_goals simp [axxs_sorted]

      have acc_sorted : List.Pairwise LE.le acc := by rw [List.pairwise_append] at axxs_sorted; simp [axxs_sorted]
      have xxs_sorted : (x :: xs).Pairwise LE.le := by rw [List.pairwise_append] at axxs_sorted; simp [axxs_sorted]
      have yys_sorted : (y :: ys).Pairwise LE.le := by rw [List.pairwise_append] at ayys_sorted; simp [ayys_sorted]
      have acc_all_le_xs : ∀ (a : Nat), a ∈ acc → ∀ (b : Nat), b ∈ x::xs → a ≤ b := by rw [List.pairwise_append] at axxs_sorted; exact axxs_sorted.right.right
      have acc_all_le_ys : ∀ (a : Nat), a ∈ acc → ∀ (b : Nat), b ∈ y::ys → a ≤ b := by rw [List.pairwise_append] at ayys_sorted; exact ayys_sorted.right.right

      have xyys_sorted : List.Pairwise LE.le (x :: y :: ys) := by
        apply List.Pairwise.cons; any_goals exact yys_sorted
        -- This is so obvious! There must be a simpler proof.
        intro a a_in_yys
        calc
          x ≤ y := by exact x_le_y
          y ≤ a := by
            apply pairwise_cons_repeat at yys_sorted
            rw [List.pairwise_cons] at yys_sorted
            apply yys_sorted.left
            exact a_in_yys

      rw [List.pairwise_append]
      apply And.intro acc_sorted
      apply And.intro xyys_sorted
      intro a a_in_acc b b_in_xyys
      by_cases h : b = x
      . apply acc_all_le_xs; exact a_in_acc; simp [b_in_xyys, h]
      . apply acc_all_le_ys; exact a_in_acc
        rw [List.mem_cons] at b_in_xyys
        apply Or.resolve_left b_in_xyys h
  )

termination_by xs ys => xs.length + ys.length


def mergesort : (xs : List Nat) -> List Nat
| [] => []
| [x] => [x]
| xs@(x::y::rest) =>
  let splitlen := xs.length/2
  let left := xs.take splitlen
  let right := xs.drop splitlen
  merge_sorted [] (mergesort left) (mergesort right)
termination_by xs => xs.length
decreasing_by
  all_goals (
    rename_i xs_eq_xyrest
    simp [xs_eq_xyrest, Nat.div_lt_self]
  )

theorem mergesort_sorted : ∀ (xs : List Nat), (mergesort xs).Pairwise LE.le
| [] => by simp [mergesort]
| [x] => by simp [mergesort]
| x::y::rest => by
    simp [mergesort]
    apply merge_sorted_sorted
    all_goals (simp; apply mergesort_sorted)
termination_by xs => xs.length
decreasing_by
  all_goals simp [Nat.div_lt_self]

theorem mergesort_perm : ∀ (xs : List Nat), xs.Perm (mergesort xs) := by
  intro
  unfold mergesort
  split; all_goals simp
  rename_i x y rest
  apply List.Perm.trans _ merge_sorted_perm; simp
  apply List.Perm.trans _ (List.Perm.append (mergesort_perm _) (mergesort_perm _))
  apply List.Perm.trans _ (by rw [List.take_append_drop])
  simp
termination_by xs => xs.length
decreasing_by
  all_goals (
    rename_i hxs
    simp [hxs, Nat.div_lt_self]
  )

#eval mergesort [5, 2, 0, 1, 1, 7, 7, 1, 2, 0, 1, 9, 7, 8, 4, 1, 8, 0, 6, 3, 3, 3, 9, 5, 7, 3, 8, 1, 8, 1, 8, 3, 5, 5, 1, 1, 9, 7, 8, 4, 4, 6, 5, 2, 1, 0, 2, 5, 0, 1, 0, 3, 8, 2, 9, 7, 7, 6, 2, 5, 0, 0, 9, 4, 1, 0, 2, 2, 6, 7, 2, 3, 7, 6, 7, 3, 7, 4, 5, 1, 8, 3, 4, 4, 1, 2, 6, 6, 1, 4, 8, 2, 5, 6, 3, 6, 0, 4, 7, 7]
