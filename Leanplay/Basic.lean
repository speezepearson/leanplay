-- open Mathlib
import Mathlib.Tactic.Ring
def split (xs : List Nat) : List Nat × List Nat := (xs.take (xs.length.div 2), xs.drop (xs.length.div 2))
theorem split_shortens_left : (x y : Nat) -> (rest : List Nat) -> (split (x::y::rest)).fst.length < (x::y::rest).length := by
  intro x y rest
  unfold split; simp
  . unfold Nat.div
    simp
    calc
      rest.length.div 2 ≤ rest.length := by apply Nat.div_le_self
      rest.length < rest.length + 1 := by rw [Nat.lt_succ]
theorem split_shortens_right : (x y : Nat) -> (rest : List Nat) -> (split (x::y::rest)).snd.length < (x::y::rest).length := by
  intro x y rest
  simp [split]
  unfold Nat.div
  split
  . apply Nat.zero_lt_succ
  . rename_i h
    apply absurd h
    simp


theorem eq_append_split (xs : List Nat) : xs = List.append (split xs).fst (split xs).snd := by
  simp [split]

-- Merge two sorted lists into a single sorted list
def merge_sorted : (acc xs ys : List Nat) -> List Nat
| acc, [], ys => acc ++ ys
| acc, xs, [] => acc ++ xs
| acc, x::xs, y::ys =>
  if x <= y then merge_sorted (acc ++ [x]) xs (y::ys )
  else merge_sorted (acc ++ [y]) (x::xs) (ys)

theorem pairwise_cons_repeat (x : Nat) (xs : List Nat) (h : (x::xs).Pairwise LE.le) : (x::x::xs).Pairwise LE.le := by
  rw [List.pairwise_cons]
  apply And.intro
  . intro a a_in_xxs
    rw [List.pairwise_cons] at h
    rw [List.mem_cons] at a_in_xxs
    apply Or.elim a_in_xxs
    . intro a_eq_x; simp [a_eq_x]
    . intro h2; apply h.left; exact h2
  . exact h

theorem merge_sorted_perm :
  ∀ (total acc xs ys: List Nat),
  total.Perm (acc ++ xs ++ ys) ->
  total.Perm (merge_sorted acc xs ys)
  := by
  let rec aux :
    (total acc xs ys: List Nat) ->
    total.Perm (acc ++ xs ++ ys) ->
    total.Perm (merge_sorted acc xs ys)
    := by
    intro total acc xs ys hperm
    unfold merge_sorted
    split
    . rw [List.append_nil] at hperm; exact hperm
    . rw [List.append_nil] at hperm; exact hperm
    . have acc_short : acc.length < total.length := by
        rename_i a b c d e f g
        calc
          acc.length ≤ acc.length + (d :: e).length := by apply Nat.le_add_right
          _ ≤ acc.length + (d :: e).length + (g.length ) := by apply Nat.le_add_right
          _ < acc.length + (d :: e).length + (g.length + 1) := by
              conv => lhs; rw [Nat.add_assoc]
              conv => rhs; rw [Nat.add_assoc]
              rw [Nat.add_lt_add_iff_left]
              rw [Nat.add_lt_add_iff_left]
              simp [Nat.lt_succ]
          _ = acc.length + (d :: e).length + (f :: g).length := by
              conv =>
                rhs
                rhs
                rw [List.length_cons]
          _ = (acc ++ d :: e).length + (f :: g).length := by rw [List.length_append]
          _ = (acc ++ d :: e ++ f :: g).length := by rw [← List.length_append]
          _ = total.length := by apply List.Perm.length_eq; apply List.Perm.symm; exact hperm
      split
      . rename_i a b c d e
        have permshuffle : total.Perm ((acc ++ [a]) ++ b ++ (c :: d)) := by
          conv =>
            rhs
            lhs
            rw [List.append_assoc]
            rw [List.singleton_append]
          exact hperm
        have : total.length - (acc.length + 1) < total.length - acc.length := by
          apply Nat.sub_lt_sub_left
          exact acc_short
          simp [Nat.lt_succ]
        exact aux total (acc ++ [a]) b (c :: d) permshuffle
      . rename_i a bs c ds e
        have permshuffle1 : (acc ++ a :: bs ++ c :: ds).Perm ((acc ++ [c]) ++ (a :: bs) ++ ds) := by
          rw [List.perm_iff_count]
          intro q
          simp [List.count_append, List.count_cons]
          split; all_goals split; all_goals ring_nf
        have permshuffle : total.Perm ((acc ++ [c]) ++ (a :: bs) ++ds) := by
          apply List.Perm.trans hperm permshuffle1
        have : total.length - (acc.length + 1) < total.length - acc.length := by
          apply Nat.sub_lt_sub_left
          exact acc_short
          simp [Nat.lt_succ]
        exact aux total (acc ++ [c]) (a :: bs) ds permshuffle
    termination_by total.length - acc.length

  intro total acc xs ys hperm
  exact aux total acc xs ys hperm

theorem merge_sorted_sorted : ∀ (xs ys acc: List Nat),
    (acc ++ xs).Pairwise LE.le ->
    (acc ++ ys).Pairwise LE.le ->
    (merge_sorted acc xs ys).Pairwise LE.le
    := by
  intro xs
  induction xs with
  | nil =>
      simp [merge_sorted]
  | cons x xs ihx =>
      intro ys
      induction ys with
      | nil =>
          simp [merge_sorted]
          intro _ axxs_sorted _
          exact axxs_sorted
      | cons y ys ihy =>
          intro acc axxs_sorted ayys_sorted
          have acc_sorted : List.Pairwise LE.le acc := by
            apply List.Pairwise.sublist (List.sublist_append_left acc (x::xs))
            exact axxs_sorted
          have xxs_sorted : (x :: xs).Pairwise LE.le := by
            apply List.Pairwise.sublist (List.sublist_append_right acc (x::xs))
            exact axxs_sorted
          have yys_sorted : (y :: ys).Pairwise LE.le := by
            apply List.Pairwise.sublist (List.sublist_append_right acc (y::ys))
            exact ayys_sorted
          have xs_sorted : xs.Pairwise LE.le := by apply List.Pairwise.of_cons xxs_sorted
          have ys_sorted : ys.Pairwise LE.le := by apply List.Pairwise.of_cons yys_sorted

          have acc_all_le_xs : ∀ (a : Nat), a ∈ acc → ∀ (b : Nat), b ∈ x::xs → a ≤ b := by
            rw [List.pairwise_append] at axxs_sorted
            exact (And.right (And.right axxs_sorted))
          have acc_all_le_ys : ∀ (a : Nat), a ∈ acc → ∀ (b : Nat), b ∈ y::ys → a ≤ b := by
            rw [List.pairwise_append] at ayys_sorted
            exact (And.right (And.right ayys_sorted))

          unfold merge_sorted
          split
          . rename_i x_le_y
            have xyys_sorted : List.Pairwise LE.le (x :: y :: ys) := by
              have y_le_yys : ∀ b : Nat, b ∈ y::ys -> y ≤ b := by
                apply And.left
                rw [← List.pairwise_cons]
                apply pairwise_cons_repeat y ys yys_sorted
              apply List.Pairwise.cons; any_goals exact yys_sorted
              intro a a_in_yys
              calc
                x ≤ y := by exact x_le_y
                y ≤ a := by apply y_le_yys; exact a_in_yys

            apply ihx
            . rw [← List.append_cons]; exact axxs_sorted
            . rw [← List.append_cons]
              rw [List.pairwise_append]
              rw [and_iff_right acc_sorted]
              rw [and_iff_right xyys_sorted]
              intro a a_in_acc b b_in_xyys

              calc
                a ≤ x := by apply acc_all_le_xs; exact a_in_acc; simp
                x ≤ b := by
                  by_cases h: x=b
                  . simp [h]
                  rw [List.mem_cons] at b_in_xyys
                  have b_in_yys : b ∈ y :: ys := by
                    apply Or.elim b_in_xyys
                    . intro h'; apply absurd (Eq.symm h') h
                    . simp
                  have x_le_yys : ∀ c : Nat, c ∈ y :: ys → x ≤ c := by
                    apply And.left
                    rw [← List.pairwise_cons]
                    exact xyys_sorted
                  apply x_le_yys
                  exact b_in_yys

          . rename_i nx_le_y
            have y_le_x : y ≤ x := by apply Nat.le_of_not_le; exact nx_le_y
            have yxxs_sorted : List.Pairwise LE.le (y :: x :: xs) := by
              have x_le_xxs : ∀ b : Nat, b ∈ x::xs -> x ≤ b := by
                apply And.left
                rw [← List.pairwise_cons]
                apply pairwise_cons_repeat x xs xxs_sorted
              apply List.Pairwise.cons; any_goals exact xxs_sorted
              intro a a_in_xxs
              calc
                y ≤ x := by exact y_le_x
                x ≤ a := by apply x_le_xxs; exact a_in_xxs

            apply ihy
            . rw [← List.append_cons]
              rw [List.pairwise_append]
              rw [and_iff_right acc_sorted]
              rw [and_iff_right yxxs_sorted]
              intro a a_in_acc b b_in_yxxs

              calc
                a ≤ y := by apply acc_all_le_ys; exact a_in_acc; simp
                y ≤ b := by
                  by_cases h: y=b
                  . simp [h]
                  rw [List.mem_cons] at b_in_yxxs
                  have b_in_xxs : b ∈ x :: xs := by
                    apply Or.elim b_in_yxxs
                    . intro h'; apply absurd (Eq.symm h') h
                    . simp
                  have y_le_xxs : ∀ c : Nat, c ∈ x :: xs → y ≤ c := by
                    apply And.left
                    rw [← List.pairwise_cons]
                    exact yxxs_sorted
                  apply y_le_xxs
                  exact b_in_xxs
            . rw [← List.append_cons]; exact ayys_sorted



def mergesort : (xs : List Nat) -> List Nat
| [] => []
| [x] => [x]
| x::y::rest =>
  let left := (split (x::y::rest)).fst
  let right := (split (x::y::rest)).snd
  merge_sorted [] (mergesort left) (mergesort right)
termination_by xs => xs.length
decreasing_by
  apply split_shortens_left
  apply split_shortens_right

theorem mergesort_sorted : ∀ (xs : List Nat), (mergesort xs).Pairwise LE.le
| [] => by simp [mergesort]
| [x] => by simp [mergesort]
| x::y::rest => by
    unfold mergesort
    apply merge_sorted_sorted
    . simp
      apply mergesort_sorted
    . simp
      apply mergesort_sorted
termination_by xs => xs.length
decreasing_by
  apply split_shortens_left
  apply split_shortens_right

theorem mergesort_perm : ∀ (xs : List Nat), (mergesort xs).Perm xs := by
  intro xs
  unfold mergesort
  split; all_goals simp
  rename_i x y rest
  apply List.Perm.symm
  apply merge_sorted_perm
  rw [List.nil_append]
  have hl : (mergesort (split (x :: y :: rest)).1).Perm (split (x :: y :: rest)).1 := by apply mergesort_perm
  have hr : (mergesort (split (x :: y :: rest)).2).Perm (split (x :: y :: rest)).2 := by apply mergesort_perm
  have speq : (x :: y :: rest) = (split (x :: y :: rest)).1 ++ (split (x :: y :: rest)).2 := by apply eq_append_split
  conv => lhs; rw [speq]
  apply List.Perm.append;
  all_goals apply List.Perm.symm
  all_goals apply mergesort_perm
termination_by xs => xs.length
decreasing_by
  rename_i h; rw [h]; apply split_shortens_left
  rename_i h; rw [h]; apply split_shortens_right

#eval mergesort [5, 2, 0, 1, 1, 7, 7, 1, 2, 0, 1, 9, 7, 8, 4, 1, 8, 0, 6, 3, 3, 3, 9, 5, 7, 3, 8, 1, 8, 1, 8, 3, 5, 5, 1, 1, 9, 7, 8, 4, 4, 6, 5, 2, 1, 0, 2, 5, 0, 1, 0, 3, 8, 2, 9, 7, 7, 6, 2, 5, 0, 0, 9, 4, 1, 0, 2, 2, 6, 7, 2, 3, 7, 6, 7, 3, 7, 4, 5, 1, 8, 3, 4, 4, 1, 2, 6, 6, 1, 4, 8, 2, 5, 6, 3, 6, 0, 4, 7, 7]
